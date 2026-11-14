import Challenge.Modexp.Submission.Proofs.CycleGlobal.MemoRun
import Challenge.Modexp.Submission.Proofs.Prepared.MemoAnswer
noncomputable section
set_option warningAsError true
namespace CycleSubmission.Global.Memo
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
/-- The unchanged recognizer reaches the exact CODECOPY/MSIZE answer tail.
The tail has a complete gas-parametric execution certificate. -/
theorem hitHandled (input : ByteArray) (hvalid : ValidInput input)
    (hmatch : MemoLogic.Matches input) :
    ∃ final : State,
      Nonempty (GasSteps (entryState input) final) ∧
        final.isDone = true ∧ final.toResult = .returned (Challenge.Modexp.spec input) := by
  refine ⟨MemoAnswer.finalState input,?_,(MemoAnswer.result input hvalid hmatch).1,
    (MemoAnswer.result input hvalid hmatch).2⟩
  exact ⟨(gasSteps_hit input hmatch).trans (MemoAnswer.steps input)⟩
#print axioms hitHandled
end CycleSubmission.Global.Memo
