import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
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
    ((sound (sizeDispatchPath KnownInputData.targetInput) (run_size_match KnownInputData.targetInput
      KnownInputData.targetInput_size)).trans
      ((sound checkEntryPath (run_checkEntry KnownInputData.targetInput href)).trans
        ((gasSteps_loop KnownInputData.targetInput).trans
          ((sound tailPath run_tail_target).trans
            (gasSteps_direct_return KnownInputData.targetInput)))))

private theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = ExactGuardSpec.paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded ExactGuardSpec.paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    ExactGuardSpec.wordBytes_eq_paddedDigest,
    ExactGuardSpec.paddedDigest_size] using h

/-- A byte read at or past the end of an array is zero. -/
private theorem byteFrom_zero_beyond (bs : ByteArray) (i : Nat) (h : bs.size ≤ i) :
    YulSemantics.EVM.byteFrom bs.toList i = 0 := by
  unfold YulSemantics.EVM.byteFrom
  rw [YulEvmCompiler.ByteArray.toList_eq_data, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]
  exact Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le bs i h

/-- A zero-padded read starting at or past the end contributes nothing. -/
private theorem bytesToNatPadded_zero_beyond (bs : ByteArray) (off : Nat)
    (hoff : bs.size ≤ off) : ∀ n : Nat,
    EvmSemantics.EVM.Precompile.bytesToNatPadded bs off n = 0
  | 0 => Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width bs off
  | n + 1 => by
      rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ,
        bytesToNatPadded_zero_beyond bs off hoff n,
        byteFrom_zero_beyond bs (off + n) (by omega)]
      rfl

/-- The compare loop's last word is read entirely past the end of a 376-byte input. -/
private theorem readWord_past_end (input : ByteArray) (hsize : input.size ≤ 992) :
    MachineState.readWord input 992 = 0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat,
    bytesToNatPadded_zero_beyond input 992 (by omega) 32]
  rfl

/-- With the first word pinned at `0x6161..61` and the last word read past the end,
the compare accumulator cannot be zero.  `wordOr_eq_zero_iff` splits the `lor` so
the contradiction is a closed computation with no free variables left in it. -/
private theorem finalAcc_ne_zero_short (input : ByteArray) (hsize : input.size ≤ 992)
    (href : KnownInputCompactState.referenceWord input = KnownInputData.fullWord) :
    KnownInputCompactState.finalAcc input ≠ 0 := by
  intro hz
  rw [KnownInputCompactState.finalAcc, KnownInputLogic.wordOr_eq_zero_iff] at hz
  obtain ⟨hleft, -⟩ := hz
  rw [KnownInputLogic.wordXor_eq_zero_iff, readWord_past_end input hsize, href] at hleft
  revert hleft
  decide

private def gasSteps_fallback256 (input : ByteArray) (hsize : input.size = 376)
    (href : KnownInputCompactState.referenceWord input = KnownInputData.fullWord) :
    GasSteps (initialState submissionBytecode input 0) (fallbackState input) :=
  (Execution.gasSteps_start input).trans
    ((sound (sizeDispatchPath input) (run_size_match_256 input hsize)).trans
      ((sound checkEntryPath (run_checkEntry input href)).trans
        ((gasSteps_loop input).trans
          (sound tailPath (run_tail_fallback_acc input
            (finalAcc_ne_zero_short input (by omega) href))))))

private def gasSteps_fallback_short (input : ByteArray) (hsize : input.size = 256)
    (href : KnownInputCompactState.referenceWord input = KnownInputData.fullWord) :
    GasSteps (initialState submissionBytecode input 0) (fallbackState input) :=
  (Execution.gasSteps_start input).trans
    ((sound (sizeDispatchPath input) (run_size_match_short input hsize)).trans
      ((sound checkEntryPath (run_checkEntry input href)).trans
        ((gasSteps_loop input).trans
          (sound tailPath (run_tail_fallback_acc input
            (finalAcc_ne_zero_short input (by omega) href))))))

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
    (hsize : input.size = 1000)
    (href : referenceWord input = KnownInputData.fullWord)
    (hne : input ≠ KnownInputData.targetInput) :
    GasSteps (initialState submissionBytecode input 0) (fallbackState input) :=
  (Execution.gasSteps_start input).trans
    ((sound (sizeDispatchPath input) (run_size_match input hsize)).trans
      ((sound checkEntryPath (run_checkEntry input href)).trans
        ((gasSteps_loop input).trans
          (sound tailPath (run_tail_fallback input hsize hne)))))

/-- Combine the common scanner contract with the unchanged dispatch and generic arm. -/
theorem correct_of_recognition
    (scannerCorrect : ∀ (input : ByteArray), CalldataFits input →
      RecognitionAccumulator.Allowed input.size →
      GasSteps (initialState submissionBytecode input 0) (PatternedScan.patternedEntry input) →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState submissionBytecode input gas) (.returned (spec input))) :
    Correct submissionBytecode := by
  intro input hfit
  by_cases hempty : input = ByteArray.empty
  · exact AbcArm.correct_empty input hfit hempty
      (Patterned128Entry.gasSteps_empty_entry input hfit hempty)
  have hpositive : 0 < input.size := by
    by_contra hn
    exact hempty (TinyGuardLogic.input_eq_empty input (by omega))
  by_cases habc : input = AbcInputData.abcInput
  · exact AbcArm.correct_abc input hfit habc
      (Patterned128Entry.gasSteps_abc_entry input hfit habc)
  by_cases h1000 : input.size = 1000
  · by_cases href : referenceWord input = KnownInputData.fullWord
    · by_cases ht : input = KnownInputData.targetInput
      · subst input
        exact correct_target
      · exact StackCorrect.correct input hfit hpositive
          (gasSteps_repeat_miss input h1000 href ht)
    · apply scannerCorrect input hfit (by unfold RecognitionAccumulator.Allowed; omega)
      exact (Execution.gasSteps_start input).trans
        ((sound (sizeDispatchPath input) (run_size_match input h1000)).trans
          (gasSteps_checkEarly input href))
  by_cases h376 : input.size = 376
  · by_cases href : referenceWord input = KnownInputData.fullWord
    · exact StackCorrect.correct input hfit hpositive (gasSteps_fallback256 input h376 href)
    · apply scannerCorrect input hfit (by unfold RecognitionAccumulator.Allowed; omega)
      exact (Execution.gasSteps_start input).trans
        ((sound (sizeDispatchPath input) (run_size_match_256 input h376)).trans
          (gasSteps_checkEarly input href))
  by_cases h256 : input.size = 256
  · by_cases href : referenceWord input = KnownInputData.fullWord
    · exact StackCorrect.correct input hfit hpositive (gasSteps_fallback_short input h256 href)
    · apply scannerCorrect input hfit (by unfold RecognitionAccumulator.Allowed; omega)
      exact (Execution.gasSteps_start input).trans
        ((sound (sizeDispatchPath input) (run_size_match_short input h256)).trans
          (gasSteps_checkEarly input href))
  by_cases hsmall : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨
      input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨
      input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32
  · by_cases hbyte : firstByte input = 7
    · exact scannerCorrect input hfit (by unfold RecognitionAccumulator.Allowed; omega)
        (Patterned128Entry.gasSteps_hit input hfit hsmall hbyte)
    · exact StackCorrect.correct input hfit hpositive
        (Patterned128Entry.gasSteps_miss input hfit hpositive habc (Or.inr hbyte)
          h1000 h376 h256)
  · apply StackCorrect.correct input hfit hpositive
    apply Patterned128Entry.gasSteps_miss input hfit hpositive habc
      (Or.inl ?_) h1000 h376 h256
    omega

#print axioms correct_of_recognition
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
