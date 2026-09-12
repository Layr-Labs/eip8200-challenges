import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1742..1767).

`CCB` (pc 2501) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1742..1748, pc 2501..2511: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1751..1757, pc 2515..2525: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1540 .JUMPDEST,
   pushAt 1541 2 2081,
   opAt 1542 (.Dup ⟨2, by decide⟩),
   opAt 1543 (.Dup ⟨0, by decide⟩),
   opAt 1544 (.Dup ⟨0, by decide⟩),
   pushAt 1545 2 3901,
   opAt 1546 .JUMP]

/-- Instructions 1758..1764, pc 2526..2535: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1547 .JUMPDEST,
   pushAt 1548 0 0,
   opAt 1549 .NOT,
   opAt 1550 .ADD,
   opAt 1551 (.Dup ⟨0, by decide⟩),
   pushAt 1552 2 2070,
   opAt 1553 .JUMPI]

/-- Instructions 1765..1767, pc 2536..2900: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1554 .POP,
   opAt 1555 .POP,
   opAt 1556 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
