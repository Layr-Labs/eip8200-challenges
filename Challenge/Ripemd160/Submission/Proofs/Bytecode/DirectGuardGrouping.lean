import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactState
import Challenge.EvmProof.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RootOverlapGuard
import Mathlib.Data.Nat.ModEq

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardGrouping

open EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

/-- Two consecutive full-word comparisons, retaining the complete accumulator. -/
theorem loopAcc_pair (input : ByteArray) (j : Nat) :
    loopAcc input (2 * j + 2) =
      UInt256.lor
        (UInt256.xor (MachineState.readWord input (64 * j + 64)) (referenceWord input))
        (UInt256.lor
          (UInt256.xor (MachineState.readWord input (64 * j + 32)) (referenceWord input))
          (loopAcc input (2 * j))) := by
  have hsecond : 32 * (2 * j + 1 + 1) = 64 * j + 64 := by omega
  have hfirst : 32 * (2 * j + 1) = 64 * j + 32 := by omega
  change UInt256.lor
    (UInt256.xor (MachineState.readWord input (32 * (2 * j + 1 + 1))) (referenceWord input))
    (UInt256.lor
      (UInt256.xor (MachineState.readWord input (32 * (2 * j + 1))) (referenceWord input))
      (loopAcc input (2 * j))) = _
  rw [hsecond, hfirst]

private theorem lor_left_comm (a b c : UInt256) :
    UInt256.lor a (UInt256.lor b c) = UInt256.lor b (UInt256.lor a c) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_lor]
  exact Nat.or_left_comm _ _ _

private theorem foldl_seed (xs : List UInt256) (a b : UInt256) :
    xs.foldl (fun acc x => UInt256.lor x acc) (UInt256.lor a b) =
      UInt256.lor a (xs.foldl (fun acc x => UInt256.lor x acc) b) := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [lor_left_comm x a b]
      exact ih a (UInt256.lor x b)

/-- Reversing the comparisons preserves every accumulator bit, for every seed accumulator. -/
theorem foldl_reverse (xs : List UInt256) (a : UInt256) :
    xs.reverse.foldl (fun acc x => UInt256.lor x acc) a =
      xs.foldl (fun acc x => UInt256.lor x acc) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih]
      exact (foldl_seed xs x a).symm

#print axioms loopAcc_pair
#print axioms foldl_reverse
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardGrouping

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
open EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

theorem shiftRight_xor_192 (a b : UInt256) :
    UInt256.shiftRight (UInt256.xor a b) (UInt256.ofNat 192) =
      UInt256.xor
        (UInt256.shiftRight a (UInt256.ofNat 192))
        (UInt256.shiftRight b (UInt256.ofNat 192)) := by
  unfold UInt256.shiftRight
  have h : ¬ (UInt256.ofNat 192).toNat ≥ 256 := by decide
  rw [if_neg h, if_neg h, if_neg h]
  unfold UInt256.xor
  congr 1
  apply Fin.ext
  change (Fin.shiftRight (Fin.xor a.val b.val) (UInt256.ofNat 192).val).val =
    (Fin.xor
      (Fin.shiftRight a.val (UInt256.ofNat 192).val)
      (Fin.shiftRight b.val (UInt256.ofNat 192).val)).val
  simp only [Fin.shiftRight, Fin.xor]
  have hs : (UInt256.ofNat 192).val.val = 192 := by decide
  rw [hs]
  change (((a.val.val ^^^ b.val.val) % UInt256.size) >>> 192) % UInt256.size =
    (((a.val.val >>> 192) % UInt256.size) ^^^
      ((b.val.val >>> 192) % UInt256.size)) % UInt256.size
  have hab : a.val.val ^^^ b.val.val < UInt256.size :=
    Nat.xor_lt_two_pow a.val.isLt b.val.isLt
  have ha : a.val.val >>> 192 < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.val.isLt
  have hb : b.val.val >>> 192 < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) b.val.isLt
  have habs : (a.val.val ^^^ b.val.val) >>> 192 < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hab
  have hshifts : (a.val.val >>> 192) ^^^ (b.val.val >>> 192) < UInt256.size :=
    Nat.xor_lt_two_pow ha hb
  rw [Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt habs,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hshifts]
  exact Nat.shiftRight_xor_distrib

abbrev finalAcc := RootOverlapGuard.finalAcc

def tailDiff (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 968) (referenceWord input)

/-- The anchor test `R * 255 + 97`: zero exactly at the repeated `0x61` word. -/
def fullTerm (input : ByteArray) : UInt256 :=
  referenceWord input * UInt256.ofNat 255 + UInt256.ofNat 97

/-- The accumulator seed built before the paired loop. -/
def seedAcc (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor (referenceWord input) (MachineState.readWord input 968))
    (fullTerm input)

/-- The three-word loop accumulation from an arbitrary seed. -/
def revFrom (input : ByteArray) (seed : UInt256) : Nat → UInt256
  | 0 => seed
  | n + 1 => UInt256.lor
      (UInt256.xor (MachineState.readWord input (960 - 96 * n)) (referenceWord input))
      (UInt256.lor
        (UInt256.xor (MachineState.readWord input (896 - 96 * n)) (referenceWord input))
        (UInt256.lor
          (UInt256.xor (MachineState.readWord input (928 - 96 * n)) (referenceWord input))
          (revFrom input seed n)))

def reverseAcc (input : ByteArray) : Nat → UInt256
  | 0 => seedAcc input
  | n + 1 => UInt256.lor
      (UInt256.xor (MachineState.readWord input (960 - 96 * n)) (referenceWord input))
      (UInt256.lor
        (UInt256.xor (MachineState.readWord input (896 - 96 * n)) (referenceWord input))
        (UInt256.lor
          (UInt256.xor (MachineState.readWord input (928 - 96 * n)) (referenceWord input))
          (reverseAcc input n)))

theorem reverseAcc_eq (input : ByteArray) (n : Nat) :
    reverseAcc input n = revFrom input (seedAcc input) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [reverseAcc, revFrom, ih]

theorem lor_comm' (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_lor]
  exact Nat.or_comm _ _

theorem revFrom_lor (input : ByteArray) (a b : UInt256) (n : Nat) :
    revFrom input (UInt256.lor a b) n = UInt256.lor a (revFrom input b n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [revFrom, ih]
      apply Challenge.EvmProof.Word.word_ext
      simp only [Challenge.EvmProof.Word.word_toNat_lor]
      ac_rfl

theorem revFrom_final (input : ByteArray) :
    revFrom input (UInt256.lor (tailDiff input) (loopAcc input 0)) 10 = finalAcc input := by
  norm_num only [revFrom, loopAcc, tailDiff, finalAcc, RootOverlapGuard.finalAcc]
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_lor]
  ac_rfl

private theorem word_toNat_mul' (x y : UInt256) :
    (x * y).toNat = (x.toNat * y.toNat) % 2 ^ 256 := by
  show (x.val * y.val).val = _
  rw [Fin.val_mul]
  rfl

theorem fullWord_anchor :
    KnownInputData.fullWord * UInt256.ofNat 255 + UInt256.ofNat 97 = 0 := by
  decide

theorem fullTerm_eq_zero (input : ByteArray) (h : fullTerm input = 0) :
    referenceWord input = KnownInputData.fullWord := by
  have hn := congrArg UInt256.toNat h
  have hc := congrArg UInt256.toNat fullWord_anchor
  unfold fullTerm at hn
  rw [Challenge.EvmProof.Word.word_toNat_add, word_toNat_mul',
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat] at hn hc
  change _ = 0 at hn hc
  apply Challenge.EvmProof.Word.word_ext
  have hr : (referenceWord input).toNat < 2 ^ 256 := (referenceWord input).val.isLt
  have hf : KnownInputData.fullWord.toNat < 2 ^ 256 := KnownInputData.fullWord.val.isLt
  have e255 : (255 : Nat) % 2 ^ 256 = 255 := by norm_num
  have e97 : (97 : Nat) % 2 ^ 256 = 97 := by norm_num
  rw [e255, e97, Nat.mod_add_mod] at hn hc
  have hm : (referenceWord input).toNat * 255 + 97 ≡
      KnownInputData.fullWord.toNat * 255 + 97 [MOD 2 ^ 256] := by
    unfold Nat.ModEq
    rw [hn, hc]
  have hm2 := Nat.ModEq.add_right_cancel' 97 hm
  have hm3 := Nat.ModEq.cancel_right_of_coprime
    (by simp [Nat.gcd_comm]) hm2
  unfold Nat.ModEq at hm3
  rwa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hf] at hm3

/-- The final accumulator splits into the anchor test and the accumulator of
the previous guard. -/
theorem reverseAcc_split (input : ByteArray) :
    reverseAcc input 10 = UInt256.lor (fullTerm input)
      (revFrom input (UInt256.xor (referenceWord input) (MachineState.readWord input 968)) 10) := by
  rw [reverseAcc_eq, seedAcc, lor_comm' (UInt256.xor _ _) (fullTerm input), revFrom_lor]

theorem xor_comm' (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val ^^^ b.val).val = (b.val ^^^ a.val).val
  rw [Fin.xor_val, Fin.xor_val, Nat.xor_comm]

private theorem lor_zero_left (a : UInt256) : UInt256.lor 0 a = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_lor]
  exact Nat.zero_or _

/-- With the anchor word in place, the old final accumulator is the loop part. -/
theorem finalAcc_of_anchor (input : ByteArray)
    (href : referenceWord input = KnownInputData.fullWord) :
    finalAcc input =
      revFrom input (UInt256.xor (referenceWord input) (MachineState.readWord input 968)) 10 := by
  rw [← revFrom_final]
  have hz : loopAcc input 0 = 0 := by
    rw [loopAcc, href]
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  rw [lor_comm' (tailDiff input), hz, lor_zero_left, tailDiff, xor_comm']

theorem reverseAcc_zero_target (input : ByteArray) (hsize : input.size = 1000)
    (h : reverseAcc input 10 = 0) : input = KnownInputData.targetInput := by
  rw [reverseAcc_split] at h
  rcases (KnownInputLogic.wordOr_eq_zero_iff _ _).1 h with ⟨hf, hloop⟩
  have href := fullTerm_eq_zero input hf
  apply (RootOverlapGuard.finalAcc_zero_iff_target input hsize).1
  change finalAcc input = 0
  rw [finalAcc_of_anchor input href]
  exact hloop

theorem reverseAcc_target_zero : reverseAcc KnownInputData.targetInput 10 = 0 := by
  have href : referenceWord KnownInputData.targetInput = KnownInputData.fullWord := by
    simpa [referenceWord, KnownInputData.expectedWord] using
      (KnownInputData.targetInput_readWord 0 (by decide))
  have hf : fullTerm KnownInputData.targetInput = 0 := by
    rw [fullTerm, href]
    exact fullWord_anchor
  have hloop := (RootOverlapGuard.finalAcc_zero_iff_target KnownInputData.targetInput
    KnownInputData.targetInput_size).2 rfl
  change finalAcc KnownInputData.targetInput = 0 at hloop
  rw [finalAcc_of_anchor _ href] at hloop
  rw [reverseAcc_split, hf, hloop]
  decide

#print axioms reverseAcc_zero_target
#print axioms reverseAcc_target_zero
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
