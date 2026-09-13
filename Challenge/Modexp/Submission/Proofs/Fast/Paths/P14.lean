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
  [opAt 1602 .JUMPDEST,
   pushAt 1603 2 2196,
   opAt 1604 (.Dup ⟨2, by decide⟩),
   opAt 1605 (.Dup ⟨0, by decide⟩),
   opAt 1606 (.Dup ⟨0, by decide⟩),
   pushAt 1607 2 4092,
   opAt 1608 .JUMP]

/-- Instructions 1888..1891, pc 2661..2670: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1609 .JUMPDEST,
   pushAt 1610 0 0,
   opAt 1611 .NOT,
   opAt 1612 .ADD,
   opAt 1613 (.Dup ⟨0, by decide⟩),
   pushAt 1614 2 2185,
   opAt 1615 .JUMPI]

/-- Instructions 1892..1894, pc 2671..3035: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1616 .POP,
   opAt 1617 .POP,
   opAt 1618 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
