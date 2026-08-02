import Challenge.RouteB
import Challenge.Sha256.Spec
set_option warningAsError true
/-!
# Direct raw-bytecode reduction for SHA-256

This is the submission-facing endpoint for Route B. A participant proves
`DirectProof code` with the generic `Reaches` block and loop combinators. The
soundness theorem then yields the challenge's canonical `Correct code` without
source semantics or compiler correctness.

Reference-specific targets and invariants live under `Reference/Proofs/RouteB`.
-/

namespace Challenge.Sha256.RouteB

open EvmSemantics.EVM

/-- Direct, compositional small-step obligation for any SHA-256 bytecode. -/
def DirectProof (code : ByteArray) : Prop :=
  Challenge.RouteB.EventuallyEvaluates
    (Input := { calldata : ByteArray // CalldataFits calldata })
    (fun calldata gas => frame code calldata.1 gas)
    (fun calldata => .returned (spec calldata.1))

/-- A direct raw-bytecode execution proof discharges the canonical challenge. -/
theorem correct_of_directProof {code : ByteArray} (h : DirectProof code) :
    Correct code := by
  intro calldata hfit
  simpa using h.sound ⟨calldata, hfit⟩

end Challenge.Sha256.RouteB
