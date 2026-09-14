import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryGateLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAccumulator

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
  let step : ∀ n, n < 14 → GasSteps (loopState input n) (loopState input (n + 1)) :=
    fun n hn => sound loopPath (run_loop_more input n hn)
  exact (GasSteps.iterateBounded 14 step).trans
    (sound loopPath (run_loop_last input))

/-- A first byte other than 7 with a size below four or exactly 1000 reaches the
first-word test. -/
private def gasSteps_matched (input : ByteArray) (hfit : CalldataFits input)
    (hbyte : firstByte input ≠ 7) (hsmall : input.size < 4 ∨ input.size = 1000) :
    GasSteps (initialState submissionBytecode input 0) (sizeMatched input) :=
  (Execution.gasSteps_start input).trans
    ((sound bytePath (run_byte_fall input hbyte)).trans
      (sound gatePath (run_gate_fall input hfit hsmall)))

/-- The repeated `0x61` word has first byte `0x61`. -/
private theorem firstByte_of_fullWord (input : ByteArray)
    (href : referenceWord input = KnownInputData.fullWord) : firstByte input ≠ 7 := by
  intro h7
  have h := firstByte_eq_byteAt input
  rw [show MachineState.readWord input 0 = referenceWord input from rfl, href, h7] at h
  revert h
  decide

def gasSteps_target :
    GasSteps (initialState submissionBytecode KnownInputData.targetInput 0)
      (returnedState KnownInputData.targetInput) :=
  have href : referenceWord KnownInputData.targetInput = KnownInputData.fullWord := by
    simpa [referenceWord, KnownInputData.expectedWord] using
      (KnownInputData.targetInput_readWord 0 (by decide))
  have hfit : CalldataFits KnownInputData.targetInput := by
    change KnownInputData.targetInput.size < 2 ^ 64
    rw [KnownInputData.targetInput_size]
    norm_num
  (gasSteps_matched KnownInputData.targetInput hfit
      (firstByte_of_fullWord _ href) (Or.inr KnownInputData.targetInput_size)).trans
    ((sound checkEntryPath (run_checkEntry KnownInputData.targetInput href)).trans
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

private def gasSteps_repeat_miss (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 1000)
    (href : referenceWord input = KnownInputData.fullWord)
    (hne : input ≠ KnownInputData.targetInput) :
    GasSteps (initialState submissionBytecode input 0) (fallbackState input) :=
  (gasSteps_matched input hfit (firstByte_of_fullWord input href) (Or.inr hsize)).trans
    ((sound checkEntryPath (run_checkEntry input href)).trans
      ((gasSteps_loop input).trans
        ((sound tailPath (run_tail_divert input hsize hne)).trans
          (sound fallbackPath (run_fallback_clear input)))))

private theorem firstByte_empty : firstByte ByteArray.empty ≠ 7 := by
  simp [firstByte, YulSemantics.EVM.byteFrom, YulEvmCompiler.ByteArray.toList_eq_data]

/-- Combine the common scanner contract with the entry dispatch and generic arm. -/
theorem correct_of_recognition
    (scannerCorrect : ∀ (input : ByteArray), CalldataFits input →
      RecognitionAccumulator.Allowed input.size →
      GasSteps (initialState submissionBytecode input 0) (PatternedScan.patternedEntry input) →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState submissionBytecode input gas) (.returned (spec input))) :
    Correct submissionBytecode := by
  intro input hfit
  by_cases hbyte : firstByte input = 7
  · have hpositive : 0 < input.size := by
      by_contra hn
      have he := TinyGuardLogic.input_eq_empty input (by omega)
      rw [he] at hbyte
      exact firstByte_empty hbyte
    have hstart : GasSteps (initialState submissionBytecode input 0) (guardEntry input) :=
      (Execution.gasSteps_start input).trans (sound bytePath (run_byte_taken input hbyte))
    by_cases hallowed : RecognitionAccumulator.Allowed input.size
    · exact scannerCorrect input hfit hallowed
        (hstart.trans (Patterned128Entry.gasSteps_allowed input hfit hallowed))
    · exact StackCorrect.correct input hfit hpositive
        (hstart.trans (Patterned128Entry.gasSteps_disallowed input hfit hbyte hallowed))
  by_cases hgate : 4 ≤ input.size ∧ input.size ≠ 1000
  · exact StackCorrect.correct input hfit (by omega)
      ((Execution.gasSteps_start input).trans
        ((sound bytePath (run_byte_fall input hbyte)).trans
          (sound gatePath (run_gate_taken input hfit hgate.1 hgate.2))))
  have hsmall : input.size < 4 ∨ input.size = 1000 := by omega
  by_cases href : referenceWord input = KnownInputData.fullWord
  · have h1000 : input.size = 1000 := by
      rcases hsmall with h | h
      · exact absurd href (EntryGateLogic.readWord_ne_fullWord input (by omega))
      · exact h
    by_cases ht : input = KnownInputData.targetInput
    · subst input
      exact correct_target
    · exact StackCorrect.correct input hfit (by omega)
        (gasSteps_repeat_miss input hfit h1000 href ht)
  have hguard : GasSteps (initialState submissionBytecode input 0) (guardEntry input) :=
    (gasSteps_matched input hfit hbyte hsmall).trans (gasSteps_checkEarly input href)
  by_cases hallowed : RecognitionAccumulator.Allowed input.size
  · exact scannerCorrect input hfit hallowed
      (hguard.trans (Patterned128Entry.gasSteps_allowed input hfit hallowed))
  have harm : GasSteps (initialState submissionBytecode input 0) (AbcArm.armEntry input) :=
    hguard.trans (Patterned128Entry.gasSteps_to_arm input hfit hallowed)
  by_cases hw : AbcArm.wordCond input = 0
  · have hs4 : input.size < 4 := by
      rcases hsmall with h | h
      · exact h
      · exact absurd hw (EntryGateLogic.wordCond_ne_zero_of_size1000 input hfit h)
    by_cases hempty : input.size = 0
    · exact AbcArm.correct_empty input hfit (TinyGuardLogic.input_eq_empty input hempty) harm
    · exact AbcArm.correct_abc input hfit
        (EntryGateLogic.wordCond_zero_size_pos input hfit (by omega) hs4 hw) harm
  · have hpositive : 0 < input.size := by
      by_contra hn
      have he := TinyGuardLogic.input_eq_empty input (by omega)
      apply hw
      rw [he]
      have hc := TinyGuardLogic.condition_empty
      exact ((KnownInputLogic.wordOr_eq_zero_iff _ _).mp hc).1
    exact StackCorrect.correct input hfit hpositive
      (harm.trans (AbcArm.gasSteps_miss input hw))

#print axioms correct_of_recognition
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
