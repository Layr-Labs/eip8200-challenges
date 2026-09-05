import Challenge.Modexp.Submission.Proofs.Fast.Guard257State
import Challenge.Modexp.Submission.Proofs.Fast.Guard257Output
import Challenge.Modexp.Submission.Proofs.Fast.Guard257Spec

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Result

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Guard257Logic Guard257State

@[simp] theorem returnedState_isDone (input : ByteArray) :
    (returnedState input).isDone = true := by
  simp [returnedState, State.isDone, State.isHalted, State.isRunning]
  rfl

theorem returnedState_result (input : ByteArray) (hvalid : ValidInput input)
    (hg : guardDiff input = 0) :
    (returnedState input).toResult = .returned (spec input) := by
  have hbound : input.size < 2 ^ 256 := hvalid.1.trans (by norm_num)
  have hm : Guard257Logic.Matches input :=
    (Guard257Logic.guardDiff_eq_zero_iff input hbound).1 hg
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned
      (MachineState.readPadded Guard257State.answerMemory 0 33) = _
  rw [Guard257Output.answerMemory_read, Guard257Spec.spec_eq hm]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Result
