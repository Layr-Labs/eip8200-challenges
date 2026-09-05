import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardBranch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardCorrect
open EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160 Challenge.EvmProof
open ExactGuardLogic ExactGuardState

private theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = ExactGuardSpec.paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded ExactGuardSpec.paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    ExactGuardSpec.wordBytes_eq_paddedDigest] using h

theorem correct : Correct submissionBytecode := by
  intro input hfit
  by_cases h : guardDiff input = 0
  · let trace := (Execution.gasSteps_start input).trans
      (ExactGuardBranch.gasSteps_match input h)
    have hbound : input.size < 2 ^ 256 := hfit.trans (by norm_num)
    have hm := (guardDiff_eq_zero_iff input hbound).1 h
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      change (withGas (returnedState input) (gas - trace.cost)).isDone = true
      simp [withGas, returnedState, initialState,
        State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded answerMemory 0 32)) at heval
    rw [answerMemory_read, ← ExactGuardSpec.spec_eq_paddedDigest_of_matches hm] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      ((Execution.gasSteps_start input).trans
        (ExactGuardBranch.gasSteps_fallback input h))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardCorrect
