import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardTail

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! Composition and the correctness theorem. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

private def sound (path : List Located) {s t : State}
    (h : run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

private def gasSteps_loop (input : ByteArray) :
    GasSteps (loopState input 0) (loopExitState input) := by
  let step : ∀ n, n < 29 → GasSteps (loopState input n) (loopState input (n + 1)) :=
    fun n hn => sound loopPath (run_loop_more input n hn)
  exact (GasSteps.iterateBounded 29 step).trans
    (sound loopPath (run_loop_last input))

def gasSteps_target :
    GasSteps (initialState submissionBytecode KnownInputData.targetInput 0)
      (returnedState KnownInputData.targetInput) :=
  have href : referenceWord KnownInputData.targetInput = KnownInputData.fullWord := by
    simpa [referenceWord, KnownInputData.expectedWord] using
      (KnownInputData.targetInput_readWord 0 (by decide))
  (Execution.gasSteps_start KnownInputData.targetInput).trans
    ((sound sizePath (run_size_match KnownInputData.targetInput
      KnownInputData.targetInput_size)).trans
      ((sound checkEntryPath (run_checkEntry KnownInputData.targetInput href)).trans
        ((gasSteps_loop KnownInputData.targetInput).trans
          ((sound tailPath run_tail_target).trans
            (sound returnPath run_return)))))

def gasSteps_fallback (input : ByteArray) (hfit : CalldataFits input)
    (hne : input ≠ KnownInputData.targetInput)
    (hpne : input ≠ PatternedInputData.patternedInput) :
    GasSteps (initialState submissionBytecode input 0) (fallbackState input) := by
  by_cases hsize : input.size = 1000
  · by_cases href : referenceWord input = KnownInputData.fullWord
    · exact (Execution.gasSteps_start input).trans
        ((sound sizePath (run_size_match input hsize)).trans
          ((sound checkEntryPath (run_checkEntry input href)).trans
            ((gasSteps_loop input).trans
              (sound tailPath (run_tail_fallback input hsize hne)))))
    · exact (Execution.gasSteps_start input).trans
        ((sound sizePath (run_size_match input hsize)).trans
          ((gasSteps_checkEarly input href).trans
            (PatternedScan.gasSteps_patterned_miss input hsize hpne)))
  · exact (Execution.gasSteps_start input).trans
      (sound sizePath (run_size_fail input hfit hsize))

private theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = ExactGuardSpec.paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded ExactGuardSpec.paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    ExactGuardSpec.wordBytes_eq_paddedDigest,
    ExactGuardSpec.paddedDigest_size] using h

theorem correct : Correct submissionBytecode := by
  intro input hfit
  by_cases h : input = KnownInputData.targetInput
  · subst input
    let trace := gasSteps_target
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, returnedState, initialState,
        State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas
      (initialState submissionBytecode KnownInputData.targetInput 0) gas)
      (.returned (MachineState.readPadded answerMemory 0 32)) at heval
    rw [answerMemory_read, ← ExactGuardSpec.spec_targetInput_eq] at heval
    rw [show ExactGuardData.targetInput = KnownInputData.targetInput by rfl] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · by_cases hp : input = PatternedInputData.patternedInput
    · subst input
      have href : referenceWord PatternedInputData.patternedInput ≠
          KnownInputData.fullWord := PatternedInputData.patterned_reference_ne
      have hsize := PatternedInputData.patternedInput_size
      let trace :=
        (Execution.gasSteps_start PatternedInputData.patternedInput).trans
          ((sound sizePath (run_size_match PatternedInputData.patternedInput hsize)).trans
            ((gasSteps_checkEarly PatternedInputData.patternedInput href).trans
              PatternedScan.gasSteps_patterned))
      refine ⟨trace.cost, fun gas hgas => ?_⟩
      have heval := eval_of_steps (trace.trace gas hgas) (by
        simp [withGas, PatternedScan.returnedState, initialState,
          State.isDone, State.isHalted, State.isRunning])
      rw [State.toResult_returned _ (by rfl)] at heval
      change Eval (withGas
        (initialState submissionBytecode PatternedInputData.patternedInput 0) gas)
        (.returned (MachineState.readPadded PatternedScan.answerMemory 0 32)) at heval
      rw [PatternedScan.answerMemory_read, ← PatternedGuardSpec.spec_patternedInput_eq] at heval
      simpa [GasCost.withGas_initialState_zero] using heval
    · exact StackCorrect.correct input hfit
        (gasSteps_fallback input hfit h hp)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
