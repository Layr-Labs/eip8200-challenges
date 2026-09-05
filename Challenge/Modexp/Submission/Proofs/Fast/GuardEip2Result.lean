import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2State
import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Output
import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Spec

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Result

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open GuardEip2Logic GuardEip2State

@[simp] theorem returnedState_isDone (input : ByteArray) :
    (returnedState input).isDone = true := by
  simp [returnedState, State.isDone, State.isHalted, State.isRunning]
  rfl

theorem returnedState_result (input : ByteArray) (hvalid : ValidInput input)
    (hg : guardDiff input = 0) :
    (returnedState input).toResult = .returned (spec input) := by
  have hbound : input.size < 2 ^ 256 := hvalid.1.trans (by norm_num)
  have hm : GuardEip2Logic.Matches input :=
    (GuardEip2Logic.guardDiff_eq_zero_iff input hbound).1 hg
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned
      (MachineState.readPadded GuardEip2State.answerMemory 0 32) = _
  rw [GuardEip2Output.answerMemory_read, GuardEip2Spec.spec_eq hm]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Result
