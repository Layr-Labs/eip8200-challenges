import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftStates
noncomputable section
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift
open EvmSemantics
@[simp] theorem headWord_uMem (z : ByteArray) (n : Nat) :
    headWord (uMem z n) n = headWord z n := by
  unfold headWord loopPC
  rw [Shift.uMem_readWord_disjoint z n 1536 (Or.inl (by omega))]
@[simp] theorem loopPC_uMem (z : ByteArray) (n : Nat) :
    loopPC (uMem z n) n = loopPC z n := by
  unfold loopPC
  rw [Shift.uMem_readWord_disjoint z n 1536 (Or.inl (by omega))]
theorem headWord_eq_of_read (a b : ByteArray) (n : Nat)
    (h : MachineState.readWord a 1536 = MachineState.readWord b 1536) :
    headWord a n = headWord b n := by
  unfold headWord loopPC
  rw [h]
end CycleSubmission.Global.Fast.Shift
