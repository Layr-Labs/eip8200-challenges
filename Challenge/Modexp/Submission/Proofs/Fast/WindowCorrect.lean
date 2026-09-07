import Challenge.Modexp.Submission.Proofs.Bytecode.WindowBodyCorrect
import Challenge.Modexp.Submission.Proofs.Fast.Setup

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Full fast/reference composition for the fixed-width route

The existing Montgomery success proof is reused verbatim.  If that fast path
declines, `Fast.Setup.gasSteps_fallback` reaches pc 1196 and the route-aware
reference-body proof takes over.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Successful execution of the pre-existing Montgomery fast path. -/
abbrev FastHandled (input : ByteArray) : Prop :=
  ∃ final : State,
    Nonempty (Challenge.EvmProof.GasSteps
      (Main.trampolineState input 1314) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input)

private theorem withGas_initialState (code cd : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas (initialState code cd 0) gas =
      initialState code cd gas := rfl

/-- Package both outer cases as one successful initial-state execution. -/
def handledOf (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (input : ByteArray) (hvalid : ValidInput input) :
    WindowBodyCorrect.Handled input := by
  by_cases hfast : Setup.FastPath input
  · rcases fastHandled input hvalid hfast with
      ⟨final, ⟨fastTrace⟩, hdone, hresult⟩
    exact ⟨final, ⟨(Main.gasSteps_entryHop input).trans fastTrace⟩,
      hdone, hresult⟩
  · let bodyEntry := (Main.gasSteps_entryHop input).trans
      (Setup.gasSteps_fallback input hfast)
    exact WindowBodyCorrect.handledOf route input hvalid bodyEntry

private noncomputable def chosenFinal (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (input : ByteArray) (hvalid : ValidInput input) : State :=
  Classical.choose (handledOf route fastHandled input hvalid)

private noncomputable def chosenTrace (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (chosenFinal route fastHandled input hvalid) :=
  Classical.choice ((Classical.choose_spec
    (handledOf route fastHandled input hvalid)).1)

private theorem chosen_isDone (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal route fastHandled input hvalid).isDone = true :=
  (Classical.choose_spec (handledOf route fastHandled input hvalid)).2.1

private theorem chosen_result (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal route fastHandled input hvalid).toResult =
      .returned (spec input) :=
  (Classical.choose_spec (handledOf route fastHandled input hvalid)).2.2

theorem submissionDirectProof (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input) :
    Challenge.Modexp.ProofSupport.Bytecode.DirectProof submissionBytecode := by
  let Input := { calldata : ByteArray // ValidInput calldata }
  have h := Challenge.EvmProof.GasSteps.toEventuallyEvaluates
    (initial := fun input : Input => initialState submissionBytecode input.1 0)
    (final := fun input : Input =>
      chosenFinal route fastHandled input.1 input.2)
    (expected := fun input : Input => .returned (spec input.1))
    (fun input => chosenTrace route fastHandled input.1 input.2)
    (fun input => chosen_isDone route fastHandled input.1 input.2)
    (fun input => chosen_result route fastHandled input.1 input.2)
  simpa [Challenge.Modexp.ProofSupport.Bytecode.DirectProof, Input,
    withGas_initialState] using h

/-- Top-level `Correct` bridge.  The concrete submission will instantiate
`route` with the appended execution proof and `fastHandled` with `Fast.Exp`. -/
theorem submission_correct_of (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input) :
    Challenge.Modexp.Correct submissionBytecode :=
  Challenge.Modexp.ProofSupport.Bytecode.correct_of_directProof
    (submissionDirectProof route fastHandled)

end Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect
