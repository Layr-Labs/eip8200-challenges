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
  · let header := Main.gasSteps_header input hvalid entry
    let entered := header.trans (route.enter input hvalid hpositive hword)
    by_cases hmatch : WindowRoute.Matches input
    · exact prepend entered (route.hit input hvalid hpositive hword hmatch)
    · let missed := entered.trans
        (route.miss input hvalid hpositive hword hmatch)
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
