import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryGateLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAccumulator
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryPrefilter

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

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
  Challenge.EvmProof.DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

private def gasSteps_loop (input : ByteArray) :
    GasSteps (loopState input 0) (loopExitState input) := by
  let step : ∀ n, n < 9 → GasSteps (loopState input n) (loopState input (n + 1)) :=
    fun n hn => sound loopPath (run_loop_more input n hn)
  exact (GasSteps.iterateBounded 9 step).trans
    (sound loopPath (run_loop_last input))

/-- A 1000-byte input whose first word is the repeated `0x61` word reaches the
seed block. -/
private def gasSteps_matched (input : ByteArray)
    (hpass : EntryPrefilter.condition input = 0) (hsize : input.size = 1000)
    (href : referenceWord input = KnownInputData.fullWord) :
    GasSteps (initialState submissionBytecode input 0) (sizeMatched input) :=
  (EntryPrefilter.gasSteps_fall input hpass).trans
    ((sound sizePath (run_size_fall input hsize)).trans
      (sound anchorPath (run_anchor_fall input href)))

def gasSteps_target :
    GasSteps (initialState submissionBytecode KnownInputData.targetInput 0)
      (returnedState KnownInputData.targetInput) :=
  have href : referenceWord KnownInputData.targetInput = KnownInputData.fullWord := by
    simpa [referenceWord, KnownInputData.expectedWord] using
      (KnownInputData.targetInput_readWord 0 (by decide))
  (gasSteps_matched KnownInputData.targetInput
      (EntryPrefilter.condition_of_fullWord _ href) KnownInputData.targetInput_size href).trans
    ((gasSteps_checkEntry KnownInputData.targetInput).trans
      ((gasSteps_loop KnownInputData.targetInput).trans
        ((sound tailPath run_tail_target).trans
          (gasSteps_direct_return KnownInputData.targetInput))))

private theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = ExactGuardSpec.paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded ExactGuardSpec.paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    ExactGuardSpec.wordBytes_eq_paddedDigest,
    ExactGuardSpec.paddedDigest_size] using h

private theorem correct_target :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode KnownInputData.targetInput gas)
        (.returned (spec KnownInputData.targetInput)) := by
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

private def gasSteps_repeat_miss (input : ByteArray)
    (hpass : EntryPrefilter.condition input = 0) (hsize : input.size = 1000)
    (href : referenceWord input = KnownInputData.fullWord)
    (hne : input ≠ KnownInputData.targetInput) :
    GasSteps (initialState submissionBytecode input 0) (fallbackState input) :=
  (gasSteps_matched input hpass hsize href).trans
    ((gasSteps_checkEntry input).trans
      ((gasSteps_loop input).trans
        ((sound tailPath (run_tail_divert input hsize href hne)).trans
          (sound fallbackPath (run_fallback_clear input)))))

/-- Combine the common scanner contract with the entry dispatch and generic arm. -/
theorem correct_of_recognition
    (scannerCorrect : ∀ (input : ByteArray), CalldataFits input →
      RecognitionAccumulator.Allowed input.size →
      GasSteps (initialState submissionBytecode input 0) (PatternedScan.patternedEntry input) →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState submissionBytecode input gas) (.returned (spec input))) :
    Correct submissionBytecode := by
  intro input hfit
  by_cases hpass : EntryPrefilter.condition input = 0
  swap
  · exact StackCorrect.correct input hfit
      (EntryPrefilter.positive_of_taken input hpass)
      (EntryPrefilter.gasSteps_taken input hpass)
  -- Every input that reaches the patterned guard is handled by the scanner or the
  -- sign-extending small-input arm.
  have fromGuard : GasSteps (initialState submissionBytecode input 0) (guardEntry input) →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
    intro hguard
    by_cases hallowed : RecognitionAccumulator.Allowed input.size
    · exact scannerCorrect input hfit hallowed
        (hguard.trans (Patterned128Entry.gasSteps_allowed input hfit hallowed))
    have harm : GasSteps (initialState submissionBytecode input 0) (AbcArm.armEntry input) :=
      hguard.trans (Patterned128Entry.gasSteps_to_arm input hfit hallowed)
    by_cases hw : AbcArm.wordCond input = 0
    · have hs4 := AbcArm.size_lt_four_of_wordCond input hfit hw
      by_cases hempty : input.size = 0
      · exact AbcArm.correct_empty input hfit (TinyGuardLogic.input_eq_empty input hempty) harm
      · have hwU : EntryGateLogic.wordCond input = 0 := by
          have h := AbcArm.wordCond_eq_U input (AbcArm.small_of_wordCond input hfit hw)
          rw [h] at hw
          exact hw
        exact AbcArm.correct_abc input hfit
          (EntryGateLogic.wordCond_zero_size_pos input hfit (by omega) hs4 hwU) harm
    · have hpositive : 0 < input.size := by
        by_contra hn
        have he := TinyGuardLogic.input_eq_empty input (by omega)
        apply hw
        rw [he]
        exact AbcArm.wordCond_empty
      exact StackCorrect.correct input hfit hpositive
        (harm.trans (AbcArm.gasSteps_miss input hw))
  by_cases h1000 : input.size = 1000
  swap
  · exact fromGuard ((EntryPrefilter.gasSteps_fall input hpass).trans
      (sound sizePath (run_size_taken input hfit h1000)))
  by_cases href : referenceWord input = KnownInputData.fullWord
  swap
  · exact fromGuard ((EntryPrefilter.gasSteps_fall input hpass).trans
      ((sound sizePath (run_size_fall input h1000)).trans
        (sound anchorPath (run_anchor_taken input href))))
  by_cases ht : input = KnownInputData.targetInput
  · subst input
    exact correct_target
  · exact StackCorrect.correct_tail input hfit (by omega)
      (spentCells input) (by simp [spentCells])
      (gasSteps_repeat_miss input hpass h1000 href ht)

#print axioms correct_of_recognition
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
