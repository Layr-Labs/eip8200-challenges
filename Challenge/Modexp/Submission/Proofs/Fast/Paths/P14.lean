import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1867..1892).

`CCB` (pc 2624) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1867..1873, pc 2624..2644: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1876..1882, pc 2560..2658: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1605 .JUMPDEST,
   pushAt 1606 2 2194,
   opAt 1607 (.Dup ⟨2, by decide⟩),
   opAt 1608 (.Dup ⟨0, by decide⟩),
   opAt 1609 (.Dup ⟨0, by decide⟩),
   pushAt 1610 2 4141,
   opAt 1611 .JUMP]

/-- Instructions 1888..1889, pc 2659..2668: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1612 .JUMPDEST,
   pushAt 1613 0 0,
   opAt 1614 .NOT,
   opAt 1615 .ADD,
   opAt 1616 (.Dup ⟨0, by decide⟩),
   pushAt 1617 2 2183,
   opAt 1618 .JUMPI]

/-- Instructions 1890..1892, pc 2669..3033: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1619 .POP,
   opAt 1620 .POP,
   opAt 1621 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
