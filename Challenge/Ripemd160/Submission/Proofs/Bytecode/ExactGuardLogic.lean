import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardData
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word
import Batteries.Data.Nat.Bitwise.Lemmas

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

/-!
# Pure logic for the exact `1000 a's` guard

This file models the bytecode's XOR/OR accumulator and, independently of any
particular instruction trace, proves that the size check plus all 32 padded
word checks characterize exactly `ExactGuardData.targetInput`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardLogic

open EvmSemantics
open EvmSemantics.EVM
open ExactGuardData

private theorem natOr_eq_zero_iff (a b : Nat) :
    a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hbit (i : Nat) :
        a.testBit i = false ∧ b.testBit i = false := by
      have := congrArg (fun n => n.testBit i) h
      simpa using this
    constructor
    · apply Nat.eq_of_testBit_eq
      intro i
      simpa using (hbit i).1
    · apply Nat.eq_of_testBit_eq
      intro i
      simpa using (hbit i).2
  · rintro ⟨rfl, rfl⟩
    decide

theorem wordOr_eq_zero_iff (a b : UInt256) :
    UInt256.lor a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hzeroNat : (0 : UInt256).toNat = 0 := by decide
    have hnat : a.toNat ||| b.toNat = 0 := by
      rw [← Challenge.EvmProof.Word.word_toNat_lor, h]
      rfl
    rcases (natOr_eq_zero_iff a.toNat b.toNat).1 hnat with ⟨ha, hb⟩
    constructor
    · apply Challenge.EvmProof.Word.word_ext
      rw [hzeroNat]
      exact ha
    · apply Challenge.EvmProof.Word.word_ext
      rw [hzeroNat]
      exact hb
  · rintro ⟨rfl, rfl⟩
    decide

private theorem word_toNat_xor (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  change (a.val ^^^ b.val).val = _
  rw [Fin.xor_val]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le
    (Nat.xor_lt_two_pow a.val.isLt b.val.isLt) (by rfl)

theorem wordXor_eq_zero_iff (a b : UInt256) :
    UInt256.xor a b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Challenge.EvmProof.Word.word_ext
    apply Nat.eq_of_xor_eq_zero
    rw [← word_toNat_xor, h]
    rfl
  · rintro rfl
    apply Challenge.EvmProof.Word.word_ext
    rw [word_toNat_xor, Nat.xor_self]
    rfl

/-- Sequential XOR/OR accumulator used by the 32 word comparisons. -/
def scanDiff (input : ByteArray) : List (Nat × UInt256) → UInt256 → UInt256
  | [], acc => acc
  | p :: ps, acc =>
      scanDiff input ps (UInt256.lor
        (UInt256.xor (MachineState.readWord input p.1) p.2) acc)

/-- The complete size-and-contents guard difference. -/
def guardDiff (input : ByteArray) : UInt256 :=
  scanDiff input checks
    (UInt256.lor
      (UInt256.xor (UInt256.ofNat input.size) (UInt256.ofNat 1000)) 0)

/-- Declarative form of the runtime guard. -/
def Matches (input : ByteArray) : Prop :=
  input.size = 1000 ∧
    ∀ p, p ∈ checks → MachineState.readWord input p.1 = p.2

private theorem scanDiff_eq_zero_iff (input : ByteArray)
    (xs : List (Nat × UInt256)) (acc : UInt256) :
    scanDiff input xs acc = 0 ↔
      acc = 0 ∧ ∀ p, p ∈ xs → MachineState.readWord input p.1 = p.2 := by
  induction xs generalizing acc with
  | nil => simp [scanDiff]
  | cons p ps ih =>
      rw [scanDiff, ih]
      simp only [wordOr_eq_zero_iff, wordXor_eq_zero_iff,
        List.mem_cons, forall_eq_or_imp]
      aesop

theorem guardDiff_eq_zero_iff (input : ByteArray)
    (hbound : input.size < 2 ^ 256) :
    guardDiff input = 0 ↔ Matches input := by
  rw [guardDiff, scanDiff_eq_zero_iff]
  simp only [wordOr_eq_zero_iff, wordXor_eq_zero_iff, and_true, Matches]
  constructor
  · rintro ⟨hsize, hwords⟩
    constructor
    · have hnat := congrArg UInt256.toNat hsize
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat] at hnat
      rw [Nat.mod_eq_of_lt hbound] at hnat
      norm_num at hnat ⊢
      exact hnat
    · exact hwords
  · rintro ⟨hsize, hwords⟩
    constructor
    · rw [hsize]
    · exact hwords

private theorem byteFrom_eq_getD (bytes : ByteArray) (i : Nat) :
    YulSemantics.EVM.byteFrom bytes.toList i = bytes[i]?.getD 0 := by
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD,
    YulEvmCompiler.ByteArray.toList_eq_data, Array.getElem?_toList]
  rfl

/-- Equal 32-byte EVM reads have equal bytes at every position in the word. -/
private theorem byteFrom_eq_of_readWord_eq (left right : ByteArray)
    (offset i : Nat) (hi : i < 32)
    (hword : MachineState.readWord left offset =
      MachineState.readWord right offset) :
    YulSemantics.EVM.byteFrom left.toList (offset + i) =
      YulSemantics.EVM.byteFrom right.toList (offset + i) := by
  apply UInt8.toNat.inj
  have hbyte := congrArg
    (fun word => (UInt256.byteAt (UInt256.ofNat i) word).toNat) hword
  rw [Challenge.EvmProof.Bytes.byteAt_readWord left offset i hi,
    Challenge.EvmProof.Bytes.byteAt_readWord right offset i hi,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat] at hbyte
  have hleft :
      (YulSemantics.EVM.byteFrom left.toList (offset + i)).toNat < 2 ^ 256 :=
    Nat.lt_trans
      (YulSemantics.EVM.byteFrom left.toList (offset + i)).toNat_lt (by norm_num)
  have hright :
      (YulSemantics.EVM.byteFrom right.toList (offset + i)).toNat < 2 ^ 256 :=
    Nat.lt_trans
      (YulSemantics.EVM.byteFrom right.toList (offset + i)).toNat_lt (by norm_num)
  rw [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hbyte
  exact hbyte

/-- The size check and all 32 padded word checks characterize one calldata. -/
theorem matches_iff_eq_targetInput (input : ByteArray) :
    Matches input ↔ input = targetInput := by
  constructor
  · rintro ⟨hsize, hwords⟩
    apply ByteArray.ext_getElem
    · simpa using hsize
    · intro i hinput htarget
      have hi : i < 1000 := by omega
      let block := i / 32
      let intra := i % 32
      have hblock : block < 32 := by
        dsimp [block]
        apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
        omega
      have hintra : intra < 32 := by
        dsimp [intra]
        exact Nat.mod_lt i (by norm_num)
      have hindex : 32 * block + intra = i := by
        dsimp [block, intra]
        exact Nat.div_add_mod i 32
      have hinputWord :
          MachineState.readWord input (32 * block) = expectedWord block :=
        hwords _ (check_mem block hblock)
      have htargetWord :
          MachineState.readWord targetInput (32 * block) = expectedWord block :=
        targetInput_readWord block hblock
      have hbyte := byteFrom_eq_of_readWord_eq input targetInput
        (32 * block) intra hintra (hinputWord.trans htargetWord.symm)
      rw [hindex, byteFrom_eq_getD, byteFrom_eq_getD,
        Challenge.EvmProof.Memory.getD0_eq_getElem input i hinput,
        Challenge.EvmProof.Memory.getD0_eq_getElem targetInput i htarget] at hbyte
      exact hbyte
  · intro hinput
    subst input
    constructor
    · exact targetInput_size
    · intro p hp
      rw [checks] at hp
      rcases List.mem_map.mp hp with ⟨block, hblock, rfl⟩
      exact targetInput_readWord block (List.mem_range.mp hblock)

/-- Runtime accumulator form of the same exact-input characterization. -/
theorem guardDiff_eq_zero_iff_targetInput (input : ByteArray)
    (hbound : input.size < 2 ^ 256) :
    guardDiff input = 0 ↔ input = targetInput :=
  (guardDiff_eq_zero_iff input hbound).trans
    (matches_iff_eq_targetInput input)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardLogic
