import Challenge.Modexp.Submission.Proofs.Fast.GuardState
import Challenge.Modexp.Submission.Proofs.Fast.GuardOutput
import Challenge.Modexp.Submission.Proofs.Fast.GuardSpec

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardResult

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open GuardLogic GuardState

@[simp] theorem returnedState_isDone (input : ByteArray) :
    (returnedState input).isDone = true := by
  simp [returnedState, State.isDone, State.isHalted, State.isRunning]
  rfl

theorem returnedState_result (input : ByteArray) (hvalid : ValidInput input)
    (hg : guardDiff input = 0) :
    (returnedState input).toResult = .returned (spec input) := by
  have hbound : input.size < 2 ^ 256 := hvalid.1.trans (by norm_num)
  have hm : GuardLogic.Matches input :=
    (GuardLogic.guardDiff_eq_zero_iff input hbound).1 hg
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned
      (MachineState.readPadded GuardState.answerMemory 0 256) = _
  rw [GuardOutput.answerMemory_read, GuardSpec.spec_eq hm]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast.GuardResult
