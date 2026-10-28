import Challenge.Ripemd160.Submission.Local20261028.RecDirectGuardGrouping
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.DirectGuard
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Control.KnownInputCompactState

theorem equality_comm (a b : UInt256) : UInt256.eq a b = UInt256.eq b a := by
  simp only [UInt256.eq, eq_comm]

theorem nat_zero_iff (a : UInt256) : a.toNat = 0 ↔ a = 0 := by
  constructor
  · exact fun h => Word.word_ext h
  · intro h; subst a; rfl

theorem nat_eq_iff (a b : UInt256) : a.toNat = b.toNat ↔ a = b :=
  ⟨Word.word_ext, fun h => congrArg UInt256.toNat h⟩

theorem equality_isZero_xor (a b : UInt256) :
    UInt256.eq a b = UInt256.isZero (UInt256.xor a b) := by
  simp only [UInt256.eq, UInt256.isZero, nat_zero_iff, nat_eq_iff,
    KnownInputLogic.wordXor_eq_zero_iff]

theorem land_isZero_lor (a b : UInt256) :
    UInt256.land (UInt256.isZero a) (UInt256.isZero b) =
      UInt256.isZero (UInt256.lor a b) := by
  simp only [UInt256.isZero, nat_zero_iff, KnownInputLogic.wordOr_eq_zero_iff]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp only [ha, hb, and_self,
    true_and, false_and, and_false, if_true, if_false]
  all_goals decide

def equalityAcc (input : ByteArray) : Nat → UInt256
  | 0 => UInt256.eq (referenceWord input) (MachineState.readWord input 968)
  | n + 1 => UInt256.land
      (UInt256.eq (MachineState.readWord input (960 - 96 * n)) (referenceWord input))
      (UInt256.land
        (UInt256.eq (MachineState.readWord input (896 - 96 * n)) (referenceWord input))
        (UInt256.land
          (UInt256.eq (MachineState.readWord input (928 - 96 * n)) (referenceWord input))
          (equalityAcc input n)))

theorem equalityAcc_reverse (input : ByteArray) (n : Nat) :
    equalityAcc input n = UInt256.isZero (reverseAcc input n) := by
  induction n with
  | zero => exact equality_isZero_xor _ _
  | succ n ih =>
    simp only [equalityAcc, reverseAcc, ih, equality_isZero_xor, land_isZero_lor]

#print axioms equalityAcc_reverse
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.DirectGuard
