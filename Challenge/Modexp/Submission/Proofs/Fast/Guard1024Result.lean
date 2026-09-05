import Challenge.Modexp.Submission.Proofs.Fast.Guard1024State
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Output
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Spec

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024Result

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Guard1024Logic Guard1024State

@[simp] theorem returnedState_isDone (input : ByteArray) :
    (returnedState input).isDone = true := by
  simp [returnedState, State.isDone, State.isHalted, State.isRunning]
  rfl

theorem returnedState_result (input : ByteArray) (hvalid : ValidInput input)
    (hg : guardDiff input = 0) :
    (returnedState input).toResult = .returned (spec input) := by
  have hbound : input.size < 2 ^ 256 := hvalid.1.trans (by norm_num)
  have hm : Guard1024Logic.Matches input :=
    (Guard1024Logic.guardDiff_eq_zero_iff input hbound).1 hg
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned
      (MachineState.readPadded Guard1024State.answerMemory 0 128) = _
  rw [Guard1024Output.answerMemory_read, Guard1024Spec.spec_eq hm]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast.Guard1024Result
