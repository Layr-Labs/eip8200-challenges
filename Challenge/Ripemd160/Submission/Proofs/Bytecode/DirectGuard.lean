import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Correct
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Correct
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Correct

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
            (gasSteps_direct_return KnownInputData.targetInput)))))

def gasSteps_fallback (input : ByteArray) (hfit : CalldataFits input)
    (hne : input ≠ KnownInputData.targetInput)
    (hpne : input ≠ PatternedInputData.patternedInput)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128) ∨ firstByte input ≠ 7)
    (hne32 : input.size ≠ 32 ∨ firstByte input ≠ 7)
    (h256 : input.size ≠ 376) (hshort : input.size ≠ 256) :
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
      ((sound sizePath (run_size_fail input hfit hsize h256 hshort)).trans
        (Patterned128Entry.gasSteps_fail input hfit hbad hne32))

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
    ((sound sizePath (run_size_match_256 input hsize)).trans
      ((sound checkEntryPath (run_checkEntry input href)).trans
        ((gasSteps_loop input).trans
          (sound tailPath (run_tail_fallback_acc input
            (finalAcc_ne_zero_short input (by omega) href))))))

private def gasSteps_fallback_short (input : ByteArray) (hsize : input.size = 256)
    (href : KnownInputCompactState.referenceWord input = KnownInputData.fullWord) :
    GasSteps (initialState submissionBytecode input 0) (fallbackState input) :=
  (Execution.gasSteps_start input).trans
    ((sound sizePath (run_size_match_short input hsize)).trans
      ((sound checkEntryPath (run_checkEntry input href)).trans
        ((gasSteps_loop input).trans
          (sound tailPath (run_tail_fallback_acc input
            (finalAcc_ne_zero_short input (by omega) href))))))

theorem correct : Correct submissionBytecode := by
  intro input hfit
  by_cases h256 : input.size = 376
  · by_cases href : KnownInputCompactState.referenceWord input =
      KnownInputData.fullWord
    · exact StackCorrect.correct input hfit
        (gasSteps_fallback256 input h256 href)
    · exact Prefix256Correct.correct input hfit h256 href
  by_cases hshort : input.size = 256
  · by_cases href : KnownInputCompactState.referenceWord input = KnownInputData.fullWord
    · exact StackCorrect.correct input hfit (gasSteps_fallback_short input hshort href)
    · exact Patterned256Correct.correct input hfit hshort href
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
    · by_cases hsize56 : input.size = 56
      · by_cases hbyte : firstByte input = 7
        · exact ShortPatternCorrect.correct56_from_patternedEntry input hfit hsize56 hbyte
            (Patterned128Entry.gasSteps_hit input hfit (by omega) hbyte)
        · exact StackCorrect.correct input hfit
            (gasSteps_fallback input hfit h hp (Or.inr hbyte) (Or.inr hbyte) h256 hshort)
      by_cases hsize120 : input.size = 120
      · by_cases hbyte : firstByte input = 7
        · exact ShortPatternCorrect.correct120_from_patternedEntry input hfit hsize120 hbyte
            (Patterned128Entry.gasSteps_hit input hfit (by omega) hbyte)
        · exact StackCorrect.correct input hfit
            (gasSteps_fallback input hfit h hp (Or.inr hbyte) (Or.inr hbyte) h256 hshort)
      by_cases hsize63 : input.size = 63
      · by_cases hbyte : firstByte input = 7
        · exact Patterned128Correct.correct_from_patternedEntry input hfit hsize63 hbyte
            (Patterned128Entry.gasSteps_hit input hfit (by omega) hbyte)
        · exact StackCorrect.correct input hfit
            (gasSteps_fallback input hfit h hp (Or.inr hbyte) (Or.inr hbyte) h256 hshort)
      by_cases hsize64 : input.size = 64
      · by_cases hbyte : firstByte input = 7
        · exact ShortPatternCorrect.correct64_from_patternedEntry input hfit hsize64 hbyte
            (Patterned128Entry.gasSteps_hit input hfit (by omega) hbyte)
        · exact StackCorrect.correct input hfit
            (gasSteps_fallback input hfit h hp (Or.inr hbyte) (Or.inr hbyte) h256 hshort)
      by_cases hsize65 : input.size = 65
      · by_cases hbyte : firstByte input = 7
        · exact ShortPatternCorrect.correct65_from_patternedEntry input hfit hsize65 hbyte
            (Patterned128Entry.gasSteps_hit input hfit (by omega) hbyte)
        · exact StackCorrect.correct input hfit
            (gasSteps_fallback input hfit h hp (Or.inr hbyte) (Or.inr hbyte) h256 hshort)
      by_cases hsize128 : input.size = 128
      · by_cases hbyte : firstByte input = 7
        · exact ShortPatternCorrect.correct128_from_patternedEntry input hfit hsize128 hbyte
            (Patterned128Entry.gasSteps_hit input hfit (by omega) hbyte)
        · exact StackCorrect.correct input hfit
            (gasSteps_fallback input hfit h hp (Or.inr hbyte) (Or.inr hbyte) h256 hshort)
      by_cases hsize32 : input.size = 32
      · by_cases hbyte : firstByte input = 7
        · exact ShortPatternCorrect.correct32_from_patternedEntry input hfit hsize32 hbyte
            (Patterned128Entry.gasSteps_hit32 input hfit hsize32 hbyte)
        · exact StackCorrect.correct input hfit
            (gasSteps_fallback input hfit h hp (Or.inr hbyte) (Or.inr hbyte) h256 hshort)
      exact StackCorrect.correct input hfit
        (gasSteps_fallback input hfit h hp
          (Or.inl ⟨hsize56, hsize120, hsize63, hsize64, hsize65, hsize128⟩)
          (Or.inl hsize32) h256 hshort)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
