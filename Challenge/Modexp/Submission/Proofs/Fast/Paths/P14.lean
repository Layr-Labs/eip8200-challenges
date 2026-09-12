import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1872..1897).

`CCB` (pc 2624) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1872..1878, pc 2624..2649: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1881..1887, pc 2560..2663: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1608 .JUMPDEST,
   pushAt 1609 2 2199,
   opAt 1610 (.Dup ⟨2, by decide⟩),
   opAt 1611 (.Dup ⟨0, by decide⟩),
   opAt 1612 (.Dup ⟨0, by decide⟩),
   pushAt 1613 2 4151,
   opAt 1614 .JUMP]

/-- Instructions 1888..1894, pc 2664..2673: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1615 .JUMPDEST,
   pushAt 1616 0 0,
   opAt 1617 .NOT,
   opAt 1618 .ADD,
   opAt 1619 (.Dup ⟨0, by decide⟩),
   pushAt 1620 2 2188,
   opAt 1621 .JUMPI]

/-- Instructions 1895..1897, pc 2674..3038: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1622 .POP,
   opAt 1623 .POP,
   opAt 1624 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
