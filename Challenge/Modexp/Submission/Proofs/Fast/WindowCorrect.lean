import Challenge.Modexp.Submission.Proofs.Bytecode.WindowBodyCorrect
import Challenge.Modexp.Submission.Proofs.Fast.Setup
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Full fast/reference composition for the fixed-width route

The early wrapper handles matching headers first. Every other header restores
the exact legacy entry at pc 1396. The Montgomery success proof is then reused
verbatim. If that fast path declines, the unchanged broad Setup fallback reaches
pc 1326 and the route-aware reference-body proof takes over.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Successful execution of the pre-existing Montgomery fast path. -/
abbrev FastHandled (input : ByteArray) : Prop :=
  ∃ final : State,
    Nonempty (Challenge.EvmProof.GasSteps
      (Main.trampolineState input 599) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input)

private theorem withGas_initialState (code cd : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas (initialState code cd 0) gas =
      initialState code cd gas := rfl

/-- A wide-modulus input (33..256 bytes, zero top limb or even) that the fast path
declines is handled from the fallback entry reached directly by `BAIL6`, with the
six live words still on the stack. -/
abbrev BigBailHandled : Prop :=
  ∀ input : ByteArray, ValidInput input →
    32 < modulusSize input → modulusSize input ≤ 256 →
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Setup.bigBailState (initialState submissionBytecode input 0) input) →
    WindowBodyCorrect.Handled input

/-- Package the complete early-hit / legacy-fast / legacy-fallback split. -/
def handledOf (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (bigBailHandled : BigBailHandled)
    (input : ByteArray) (hvalid : ValidInput input) :
    WindowBodyCorrect.Handled input := by
  by_cases hzero : modulusSize input = 0
  · exact EarlyWordCorrect.zero input hzero
  ·
    by_cases hmatch : WindowTwentyOneInput.Matches input
    · exact EarlyWordCorrect.hit input hmatch
    · by_cases hfast : Setup.FastPath input
      · rcases fastHandled input hvalid hfast with
          ⟨final, ⟨fastTrace⟩, hdone, hresult⟩
        exact ⟨final, ⟨(EarlyWordCorrect.legacy input hmatch (Nat.pos_of_ne_zero hzero)).trans fastTrace⟩,
          hdone, hresult⟩
      · rcases Setup.gasSteps_fallback input hvalid hfast with
          ⟨_, steps⟩ | ⟨h32, hupper, steps⟩
        · exact WindowBodyCorrect.handledOf route input hvalid
            ((EarlyWordCorrect.legacy input hmatch (Nat.pos_of_ne_zero hzero)).trans steps)
        · exact bigBailHandled input hvalid h32 hupper
            ((EarlyWordCorrect.legacy input hmatch (Nat.pos_of_ne_zero hzero)).trans steps)

private noncomputable def chosenFinal (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (bigBailHandled : BigBailHandled)
    (input : ByteArray) (hvalid : ValidInput input) : State :=
  Classical.choose (handledOf route fastHandled bigBailHandled input hvalid)

private noncomputable def chosenTrace (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (bigBailHandled : BigBailHandled)
    (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (chosenFinal route fastHandled bigBailHandled input hvalid) :=
  Classical.choice ((Classical.choose_spec
    (handledOf route fastHandled bigBailHandled input hvalid)).1)

private theorem chosen_isDone (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (bigBailHandled : BigBailHandled)
    (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal route fastHandled bigBailHandled input hvalid).isDone = true :=
  (Classical.choose_spec (handledOf route fastHandled bigBailHandled input hvalid)).2.1

private theorem chosen_result (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (bigBailHandled : BigBailHandled)
    (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal route fastHandled bigBailHandled input hvalid).toResult =
      .returned (spec input) :=
  (Classical.choose_spec (handledOf route fastHandled bigBailHandled input hvalid)).2.2

theorem submissionDirectProof (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (bigBailHandled : BigBailHandled) :
    Challenge.Modexp.ProofSupport.Bytecode.DirectProof submissionBytecode := by
  let Input := { calldata : ByteArray // ValidInput calldata }
  have h := Challenge.EvmProof.GasSteps.toEventuallyEvaluates
    (initial := fun input : Input => initialState submissionBytecode input.1 0)
    (final := fun input : Input =>
      chosenFinal route fastHandled bigBailHandled input.1 input.2)
    (expected := fun input : Input => .returned (spec input.1))
    (fun input => chosenTrace route fastHandled bigBailHandled input.1 input.2)
    (fun input => chosen_isDone route fastHandled bigBailHandled input.1 input.2)
    (fun input => chosen_result route fastHandled bigBailHandled input.1 input.2)
  simpa [Challenge.Modexp.ProofSupport.Bytecode.DirectProof, Input,
    withGas_initialState] using h

/-- Top-level `Correct` bridge.  The concrete submission will instantiate
`route` with the appended execution proof, `fastHandled` with `Fast.Exp` and
`bigBailHandled` with the wide-modulus fallback's correctness from its direct entry. -/
theorem submission_correct_of (route : WindowRoute.Route)
    (fastHandled : ∀ input : ByteArray, ValidInput input →
      Setup.FastPath input → FastHandled input)
    (bigBailHandled : BigBailHandled) :
    Challenge.Modexp.Correct submissionBytecode :=
  Challenge.Modexp.ProofSupport.Bytecode.correct_of_directProof
    (submissionDirectProof route fastHandled bigBailHandled)

end Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect
