import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactState
import Challenge.EvmProof.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RootOverlapGuard

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

def reverseAcc (input : ByteArray) : Nat → UInt256
  | 0 => UInt256.lor (tailDiff input) (loopAcc input 0)
  | n + 1 => UInt256.lor
      (UInt256.xor (MachineState.readWord input (928 - 64 * n)) (referenceWord input))
      (UInt256.lor
        (UInt256.xor (MachineState.readWord input (960 - 64 * n)) (referenceWord input))
        (reverseAcc input n))

theorem reverseAcc_final (input : ByteArray) : reverseAcc input 15 = finalAcc input := by
  norm_num only [reverseAcc, loopAcc, tailDiff, finalAcc, RootOverlapGuard.finalAcc]
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_lor]
  ac_rfl

#print axioms reverseAcc_final
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
