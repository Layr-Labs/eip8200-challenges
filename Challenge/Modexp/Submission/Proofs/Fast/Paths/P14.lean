import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1790..1815).

`CCB` (pc 2542) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1790..1796, pc 2542..2552: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1799..1805, pc 2560..2566: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1570 .JUMPDEST,
   pushAt 1571 2 2117,
   opAt 1572 (.Dup ⟨2, by decide⟩),
   opAt 1573 (.Dup ⟨0, by decide⟩),
   opAt 1574 (.Dup ⟨0, by decide⟩),
   pushAt 1575 2 4055,
   opAt 1576 .JUMP]

/-- Instructions 1806..1812, pc 2567..2576: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1577 .JUMPDEST,
   pushAt 1578 0 0,
   opAt 1579 .NOT,
   opAt 1580 .ADD,
   opAt 1581 (.Dup ⟨0, by decide⟩),
   pushAt 1582 2 2106,
   opAt 1583 .JUMPI]

/-- Instructions 1813..1815, pc 2577..2941: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1584 .POP,
   opAt 1585 .POP,
   opAt 1586 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
