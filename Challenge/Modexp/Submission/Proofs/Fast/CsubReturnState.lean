import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubModel

set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub
open EvmSemantics EvmSemantics.EVM

/-- Expose the returned state without unfolding the conditional memory
transformer at a concrete, potentially large caller memory expression. -/
theorem csReturnedState_eq_result (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) :
    csReturnedState s memory n n pdst ret rest =
      { s with
        pc := ret
        stack := rest
        memory := csResultMemory memory n pdst.toNat } := by
  simp only [csReturnedState, csResultMemory, subReturnedState, subResultMemory]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
