import Challenge.Modexp.Submission.Proofs.Fast.GuardBN254State
import Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Output
import Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Spec

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Result

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open GuardBN254Logic GuardBN254State

@[simp] theorem returnedState_isDone (input : ByteArray) :
    (returnedState input).isDone = true := by
  simp [returnedState, State.isDone, State.isHalted, State.isRunning]
  rfl

theorem returnedState_result (input : ByteArray) (hvalid : ValidInput input)
    (hg : guardDiff input = 0) :
    (returnedState input).toResult = .returned (spec input) := by
  have hbound : input.size < 2 ^ 256 := hvalid.1.trans (by norm_num)
  have hm : GuardBN254Logic.Matches input :=
    (GuardBN254Logic.guardDiff_eq_zero_iff input hbound).1 hg
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned
      (MachineState.readPadded GuardBN254State.answerMemory 0 32) = _
  rw [GuardBN254Output.answerMemory_read, GuardBN254Spec.spec_eq hm]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Result
