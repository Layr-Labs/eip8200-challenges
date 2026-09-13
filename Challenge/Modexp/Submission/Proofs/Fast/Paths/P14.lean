import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1869..1894).

`CCB` (pc 2624) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1869..1875, pc 2624..2646: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1878..1884, pc 2560..2660: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1603 .JUMPDEST,
   pushAt 1604 2 2196,
   opAt 1605 (.Dup ⟨2, by decide⟩),
   opAt 1606 (.Dup ⟨0, by decide⟩),
   opAt 1607 (.Dup ⟨0, by decide⟩),
   pushAt 1608 2 4092,
   opAt 1609 .JUMP]

/-- Instructions 1888..1891, pc 2661..2670: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1610 .JUMPDEST,
   pushAt 1611 0 0,
   opAt 1612 .NOT,
   opAt 1613 .ADD,
   opAt 1614 (.Dup ⟨0, by decide⟩),
   pushAt 1615 2 2185,
   opAt 1616 .JUMPI]

/-- Instructions 1892..1894, pc 2671..3035: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1617 .POP,
   opAt 1618 .POP,
   opAt 1619 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
