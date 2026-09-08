import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1742..1767).

`CCB` (pc 2863) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1742..1748, pc 2863..2873: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1731 .JUMPDEST,
   pushAt 1732 2 2869,
   opAt 1733 (.Dup ⟨1, by decide⟩),
   opAt 1734 (.Dup ⟨0, by decide⟩),
   opAt 1735 (.Dup ⟨0, by decide⟩),
   pushAt 1736 2 2462,
   opAt 1737 .JUMP]

/-- Instructions 1749..1750, pc 2874..2876: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1738 .JUMPDEST,
   pushAt 1739 1 8]

/-- Instructions 1751..1757, pc 2877..2887: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1740 .JUMPDEST,
   pushAt 1741 2 2883,
   opAt 1742 (.Dup ⟨2, by decide⟩),
   opAt 1743 (.Dup ⟨0, by decide⟩),
   opAt 1744 (.Dup ⟨0, by decide⟩),
   pushAt 1745 2 1939,
   opAt 1746 .JUMP]

/-- Instructions 1758..1764, pc 2888..2897: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1747 .JUMPDEST,
   pushAt 1748 0 0,
   opAt 1749 .NOT,
   opAt 1750 .ADD,
   opAt 1751 (.Dup ⟨0, by decide⟩),
   pushAt 1752 3 2872,
   opAt 1753 .JUMPI]

/-- Instructions 1765..1767, pc 2898..2900: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1754 .POP,
   opAt 1755 .POP,
   opAt 1756 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
