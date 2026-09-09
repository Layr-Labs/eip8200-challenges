import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-!
# Reference-body correctness with the fixed-width route

This module composes the new route with the unchanged one-word and wide-modulus
proofs.  It intentionally does not define any concrete route instructions.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowBodyCorrect

open EvmSemantics
open EvmSemantics.EVM

/-- A complete successful execution from the submission's initial state. -/
abbrev Handled (input : ByteArray) : Prop :=
  ∃ final : State,
    Nonempty (Challenge.EvmProof.GasSteps
      (initialState submissionBytecode input 0) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input)

/-- The old nonzero one-word proof, factored at pc 517 so it can follow a miss
from the appended route.  Every lemma used below is inherited unchanged from
`WordCorrect`. -/
def gasSteps_wordNonzeroFromEntry (input : ByteArray)
    (hvalid : ValidInput input) (hmsize : 0 < modulusSize input)
    (hword : modulusSize input ≤ 32) (hmodpos : 0 < Word.modulusValue input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (WordExit.wordFinalState input (WordCorrect.wordResult input)
        (WordCorrect.wordBase input)) := by
  let start := Word.gasSteps_start input hvalid hmsize hword hmodpos
  let setup := Word.gasSteps_baseSetup input
  let baseLoop := Word.gasSteps_baseLoop input hvalid
  let baseFinish : Challenge.EvmProof.GasSteps
      (Word.baseLoopState input (baseSize input) (WordCorrect.wordBase input))
      (Word.expLoopState input 0 (WordCorrect.wordInitialAcc input)
        (WordCorrect.wordBase input)) := by
    simpa [WordCorrect.wordBase, WordCorrect.wordInitialAcc] using
      Word.gasSteps_baseFinish input (WordCorrect.wordBase input)
        hvalid hword
  let exponentLoop : Challenge.EvmProof.GasSteps
      (Word.expLoopState input 0 (WordCorrect.wordInitialAcc input)
        (WordCorrect.wordBase input))
      (Word.expLoopState input (exponentSize input)
        (WordCorrect.wordResult input) (WordCorrect.wordBase input)) := by
    simpa [WordCorrect.wordResult] using
      WordLoops.gasSteps_expLoop input (WordCorrect.wordInitialAcc input)
        (WordCorrect.wordBase input) hvalid
  let finish := WordExit.gasSteps_expFinish input
    (WordCorrect.wordResult input) (WordCorrect.wordBase input) hvalid hword
  exact (((((start.trans setup).trans baseLoop).trans baseFinish).trans
    exponentLoop).trans finish)

/-- The old one-word implementation is a complete fallback from pc 517. -/
def legacyWordHandled (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (Dispatch.wordEntryState input) final) ∧
        final.isDone = true ∧ final.toResult = .returned (spec input) := by
  by_cases hzero : Word.modulusValue input = 0
  · exact ⟨Word.zeroModulusFinalState input,
      ⟨Word.gasSteps_zeroModulus input hvalid hmsize hword hzero⟩,
      Word.zeroModulusFinalState_isDone input,
      Word.zeroModulusFinalState_result input hmsize hzero⟩
  · have hmodpos : 0 < Word.modulusValue input := by omega
    exact ⟨WordExit.wordFinalState input (WordCorrect.wordResult input)
        (WordCorrect.wordBase input),
      ⟨gasSteps_wordNonzeroFromEntry input hvalid hmsize hword hmodpos⟩,
      WordExit.wordFinalState_isDone input (WordCorrect.wordResult input)
        (WordCorrect.wordBase input),
      WordCorrect.wordFinalState_result input hvalid hmsize hword hmodpos⟩

def zeroExponentHandled (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hzero : exponentSize input = 0)
    (hmodpos : 0 < Word.modulusValue input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps (Main.headerState input) final) ∧
        final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let acc := WordCorrect.wordInitialAcc input
  have hmodpos' : 0 < Dispatch.modulusValue input := by
    simpa [Dispatch.modulusValue, Word.modulusValue, Word.modulusOffset,
      Word.expOffset] using hmodpos
  let prefix := Dispatch.gasSteps_zeroExponentPrefix input hvalid hpositive
    hword hzero hmodpos'
  let baseFinish :
      Challenge.EvmProof.GasSteps (Dispatch.zeroExponentBaseFinishState input)
        (Word.expLoopState input 0 acc 0) := by
    simpa [acc, Dispatch.zeroExponentBaseFinishState,
      Dispatch.modulusValue, Word.modulusValue, Word.modulusOffset,
      Word.expOffset, Word.baseFinishDispatchState, Word.baseLoopState,
      Dispatch.wordEntryState, Word.nonzeroState, Word.callerRest,
      WordCorrect.wordInitialAcc] using
      (Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka Word.baseFinishTailPath rfl rfl
        (Word.run_baseFinishTail input 0 hvalid hword) rfl
        deployAddress_not_precompile)
  let exponentLoop :
      Challenge.EvmProof.GasSteps (Word.expLoopState input 0 acc 0)
        (Word.expLoopState input (exponentSize input) acc 0) := by
    simpa [acc, WordLoops.expAfter, hzero] using
      WordLoops.gasSteps_expLoop input acc 0 hvalid
  let finish := WordExit.gasSteps_expFinish input acc 0 hvalid hword
  let trace := ((prefix.trans baseFinish).trans exponentLoop).trans finish
  have hacc : acc = WordCorrect.wordResult input := by
    symm
    simp [acc, WordCorrect.wordResult, WordCorrect.wordInitialAcc,
      WordLoops.expAfter, hzero]
  have hbase :
      (WordExit.wordFinalState input acc 0).toResult =
        (WordExit.wordFinalState input acc (WordCorrect.wordBase input)).toResult := by
    rw [State.toResult_returned _ (by rfl), State.toResult_returned _ (by rfl)]
    rfl
  have hresult :
      (WordExit.wordFinalState input acc 0).toResult =
        .returned (spec input) := by
    calc
      (WordExit.wordFinalState input acc 0).toResult =
          (WordExit.wordFinalState input acc
            (WordCorrect.wordBase input)).toResult := hbase
      _ = (WordExit.wordFinalState input (WordCorrect.wordResult input)
          (WordCorrect.wordBase input)).toResult := by rw [hacc]
      _ = .returned (spec input) :=
        WordCorrect.wordFinalState_result input hvalid hpositive hword hmodpos
  exact ⟨WordExit.wordFinalState input acc 0, ⟨trace⟩,
    WordExit.wordFinalState_isDone input acc 0, hresult⟩

/-- Compose an initial-state prefix with a packaged successful suffix. -/
private theorem prepend {input : ByteArray} {middle : State}
    (entryTrace : Challenge.EvmProof.GasSteps
      (initialState submissionBytecode input 0) middle)
    (suffix : ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps middle final) ∧
        final.isDone = true ∧ final.toResult = .returned (spec input)) :
    Handled input := by
  rcases suffix with ⟨final, ⟨tail⟩, hdone, hresult⟩
  exact ⟨final, ⟨entryTrace.trans tail⟩, hdone, hresult⟩

/-- Correctness of the complete reference body when its one-word dispatch is
replaced by a route satisfying `WindowRoute.Route`. -/
def handledOf (route : WindowRoute.Route) (input : ByteArray)
    (hvalid : ValidInput input)
    (entry : Challenge.EvmProof.GasSteps
      (initialState submissionBytecode input 0)
      (Main.trampolineState input 1196)) : Handled input := by
  by_cases hzeroSize : modulusSize input = 0
  · exact ⟨Dispatch.zeroSizeFinalState input,
      ⟨Dispatch.gasSteps_zeroSize_total input hvalid hzeroSize entry⟩,
      Dispatch.zeroSizeFinalState_isDone input,
      Dispatch.zeroSizeFinalState_result input hzeroSize⟩
  have hpositive : 0 < modulusSize input := by omega
  by_cases hword : modulusSize input ≤ 32
  · by_cases hzeroExp : exponentSize input = 0
    · by_cases hzeroModulus : Word.modulusValue input = 0
      · have hzeroModulus' : Dispatch.modulusValue input = 0 := by
          simpa [Dispatch.modulusValue, Word.modulusValue,
            Word.modulusOffset, Word.expOffset] using hzeroModulus
        let header := Main.gasSteps_header input hvalid entry
        let prefix := Dispatch.gasSteps_zeroExponentLegacyPrefix input
          hvalid hpositive hword hzeroExp hzeroModulus'
        let suffix := Word.gasSteps_zeroModulus input hvalid hpositive hword
          hzeroModulus
        exact prepend header
          ⟨Word.zeroModulusFinalState input, ⟨prefix.trans suffix⟩,
            Word.zeroModulusFinalState_isDone input,
            Word.zeroModulusFinalState_result input hpositive hzeroModulus⟩
      · have hmodpos : 0 < Word.modulusValue input := by omega
        exact prepend (Main.gasSteps_header input hvalid entry)
          (zeroExponentHandled input hvalid hpositive hword hzeroExp hmodpos)
    have hexppos : 0 < exponentSize input := by omega
    let header := Main.gasSteps_header input hvalid entry
    let entered := header.trans
      (route.enter input hvalid hpositive hword hexppos)
    by_cases hmatch : WindowRoute.Matches input
    · exact prepend entered
        (route.hit input hvalid hpositive hword hexppos hmatch)
    · let missed := entered.trans
        (route.miss input hvalid hpositive hword hexppos hmatch)
      exact prepend missed (legacyWordHandled input hvalid hpositive hword)
  · have hbig : 32 < modulusSize input := by omega
    by_cases hzeroModulus : Word.modulusValue input = 0
    · exact ⟨SubmissionCorrect.bigZeroFinalState input,
        ⟨SubmissionCorrect.gasSteps_bigZeroTotal input hvalid hbig
          hzeroModulus entry⟩,
        SubmissionCorrect.zeroFinalState_isDone input (baseSize input)
          (exponentSize input) (modulusSize input) 96
          (Word.expOffset input) (Word.modulusOffset input)
          SubmissionCorrect.bigReturnDest (SubmissionCorrect.bigRest input),
        BigZeroCorrect.zeroFinalState_result input
          SubmissionCorrect.bigReturnDest (SubmissionCorrect.bigRest input)
          hvalid hbig hzeroModulus⟩
    · have hmodpos : 0 < Word.modulusValue input := by omega
      exact ⟨SubmissionCorrect.bigCompletedState input,
        ⟨SubmissionCorrect.gasSteps_bigNonzeroTotal input hvalid hbig
          hmodpos entry⟩,
        SubmissionCorrect.completedState_isDone input (baseSize input)
          (exponentSize input) (modulusSize input) 96
          (Word.expOffset input) (Word.modulusOffset input)
          SubmissionCorrect.bigReturnDest (SubmissionCorrect.bigRest input),
        BigSerializeCorrect.completedState_result input
          SubmissionCorrect.bigReturnDest (SubmissionCorrect.bigRest input)
          hvalid hbig hmodpos⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowBodyCorrect
