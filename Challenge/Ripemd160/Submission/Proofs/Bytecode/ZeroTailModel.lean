import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
Zero-padded final-word comparison for the iter66 candidate.  The fourteen
PUSH32 literals below are bytes [25,57) of each row_hex in
reports/ripemd160-iter66-zero-tail/candidate-layout.json (byte 24 is PUSH32).
The reverse scanner and every preceding full-word check are unchanged.
This model is artifact-independent: it makes no claim about instruction sites.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ZeroTailModel

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PatternedInputData PatternedWordData RecognitionAccumulator

/-- The exact zero-padded PUSH32 comparison literal in each candidate row. -/
def expectedLast : Nat → UInt256
  | 1 => 0x0700000000000000000000000000000000000000000000000000000000000000
  | 31 => 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d00
  | 32 => 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82
  | 55 => 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5000000000000000000
  | 56 => 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa0000000000000000
  | 63 => 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd00
  | 64 => 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd22
  | 65 => 0x4700000000000000000000000000000000000000000000000000000000000000
  | 119 => 0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf015000000000000000000
  | 120 => 0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a0000000000000000
  | 128 => 0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef3183d62
  | 256 => 0x678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf0429597ea3c8ed
  | 376 => 0xf2173c6186abd0f51a3f6489aed3f81d42678cb1d6fb20450000000000000000
  | 1000 => 0x88add2f71c41668b000000000000000000000000000000000000000000000000
  | _ => 0

/-- The new tail check has no post-XOR right shift. -/
def tailDiff (input : ByteArray) (n : Nat) : UInt256 :=
  UInt256.xor (expectedLast n)
    (MachineState.readWord input (32 * DirectLiteralModel.last n))

def result (input : ByteArray) (n : Nat) : UInt256 :=
  ReverseLiteralRaw.rev input (tailDiff input n) (DirectLiteralModel.last n)

/-- Reading a prefix is the patterned byte before its end and zero after it. -/
theorem byteFrom_reference (n i : Nat) (hn : n ≤ 1000) :
    YulSemantics.EVM.byteFrom (reference n).toList i =
      if i < n then expectedByte i else 0 := by
  by_cases hi : i < n
  · rw [if_pos hi, TailProjection.byteFrom_getElem (reference n) i
      (by rw [reference_size n hn]; exact hi)]
    simp only [reference, ByteArray.getElem_extract, Nat.zero_add]
    exact patternedInput_getElem i (by rw [patternedInput_size]; omega)
  · rw [if_neg hi, YulEvmCompiler.ByteArray.toList_eq_data]
    unfold YulSemantics.EVM.byteFrom
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getElem?_eq_none (by
        change (reference n).size ≤ i
        rw [reference_size n hn]
        omega)]
    rfl

/-- Small computational bridge: evaluate only the requested bytes, not the
1000-byte concrete ByteArray or its extraction implementation. -/
theorem bytesToNatPadded_reference_formula (n off width : Nat) (hn : n ≤ 1000) :
    Precompile.bytesToNatPadded (reference n) off width =
      (List.range width).foldl
        (fun acc k => acc * 256 +
          (if off + k < n then expectedByte (off + k) else 0).toNat) 0 := by
  induction width with
  | zero => simp
  | succ width ih =>
    rw [Bytes.bytesToNatPadded_succ, ih, byteFrom_reference n _ hn,
      List.range_succ, List.foldl_append]
    rfl

/-- Kernel-checked agreement of all fourteen literal rows with canonical reads. -/
theorem expectedLast_reference (n : Nat) (hn : Allowed n) :
    expectedLast n = MachineState.readWord (reference n) (32 * DirectLiteralModel.last n) := by
  have hb := allowed_bounds n hn
  symm
  apply Word.word_ext
  rw [Bytes.readWord_toNat, bytesToNatPadded_reference_formula _ _ _ hb.2]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> decide

/-- Reverse OR accumulation is zero iff its initial value and every retained
full-word difference are zero. No word check is dropped. -/
theorem rev_zero_iff (input : ByteArray) (a : UInt256) (k : Nat) :
    ReverseLiteralRaw.rev input a k = 0 ↔
      a = 0 ∧ ∀ j, j < k → DirectLiteralModel.diff input j = 0 := by
  induction k generalizing a with
  | zero => simp [ReverseLiteralRaw.rev]
  | succ k ih =>
    rw [ReverseLiteralRaw.rev, ih, KnownInputLogic.wordOr_eq_zero_iff]
    constructor
    · rintro ⟨⟨hk, ha⟩, hprev⟩
      refine ⟨ha, ?_⟩
      intro j hj
      by_cases he : j = k
      · subst j; exact hk
      · exact hprev j (by omega)
    · rintro ⟨ha, hall⟩
      exact ⟨⟨hall k (by omega), ha⟩, fun j hj => hall j (by omega)⟩

/-- Every earlier load is a complete word of the canonical prefix. -/
theorem fullword_reference (n j : Nat) (hn : Allowed n)
    (hj : j < DirectLiteralModel.last n) :
    MachineState.readWord (reference n) (32 * j) = expectedWordAt j := by
  have hb := allowed_bounds n hn
  have hfit : 32 * j + 32 ≤ n := by
    unfold DirectLiteralModel.last at hj
    omega
  rw [← PatternedWordLogic.readWord_patterned]
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat,
    bytesToNatPadded_reference n (32 * j) 32 hb.2 hfit]

/-- The zero-tail scanner recognizes exactly the canonical input at each
allowed size, including partial rows; the size hypothesis is essential. -/
theorem result_zero_iff (input : ByteArray) (n : Nat) (hn : Allowed n)
    (hsize : input.size = n) : result input n = 0 ↔ input = reference n := by
  have hb := allowed_bounds n hn
  rw [result, rev_zero_iff]
  constructor
  · rintro ⟨htail, hfull⟩
    have hlast : MachineState.readWord input (32 * DirectLiteralModel.last n) =
        MachineState.readWord (reference n) (32 * DirectLiteralModel.last n) := by
      rw [tailDiff, KnownInputLogic.wordXor_eq_zero_iff] at htail
      exact htail.symm.trans (expectedLast_reference n hn)
    apply AbcRecognition.byteArray_eq_of_readWord_cover input (reference n)
    · rw [reference_size n hb.2]
      exact hsize
    · intro j hj
      have hjle : j ≤ DirectLiteralModel.last n := by
        rw [hsize] at hj
        unfold DirectLiteralModel.last
        omega
      by_cases he : j = DirectLiteralModel.last n
      · subst j; exact hlast
      · have hjlt : j < DirectLiteralModel.last n := by omega
        have heq := hfull j hjlt
        rw [DirectLiteralModel.diff, KnownInputLogic.wordXor_eq_zero_iff] at heq
        exact heq.trans (fullword_reference n j hn hjlt).symm
  · rintro rfl
    constructor
    · rw [tailDiff, KnownInputLogic.wordXor_eq_zero_iff]
      exact expectedLast_reference n hn
    · intro j hj
      rw [DirectLiteralModel.diff, KnownInputLogic.wordXor_eq_zero_iff]
      exact fullword_reference n j hn hj

#print axioms expectedLast_reference
#print axioms rev_zero_iff
#print axioms fullword_reference
#print axioms result_zero_iff

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ZeroTailModel
