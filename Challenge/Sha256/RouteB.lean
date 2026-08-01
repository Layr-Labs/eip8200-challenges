import Challenge.RouteB
import Challenge.Sha256.Bytecode
import Challenge.Sha256.Statement
set_option warningAsError true
/-!
# Direct raw-bytecode reduction for SHA-256

This is the submission-facing endpoint for Route B. A participant proves
`DirectProof code` with the generic `Reaches` block and loop combinators. The
soundness theorem then yields the challenge's canonical `Correct code` without
source semantics or compiler correctness.

`referenceDirectGoal` fixes the first concrete target to the frozen reference
artifact. Its padding, schedule, compression-round, block-loop, and output
invariants are the next proof layer.
-/

namespace Challenge.Sha256.RouteB

open EvmSemantics.EVM

/-- Direct, compositional small-step obligation for any SHA-256 bytecode. -/
def DirectProof (code : ByteArray) : Prop :=
  Challenge.RouteB.EventuallyEvaluates
    (fun calldata gas => frame code calldata gas)
    (fun calldata => .returned (spec calldata))

/-- A direct raw-bytecode execution proof discharges the canonical challenge. -/
theorem correct_of_directProof {code : ByteArray} (h : DirectProof code) :
    Correct code :=
  h.sound

/-- The first Route B target: the frozen bytecode generated from the reference
Yul, treated only as raw bytes from this point onward. -/
def referenceDirectGoal : Prop := DirectProof referenceBytecode

end Challenge.Sha256.RouteB
