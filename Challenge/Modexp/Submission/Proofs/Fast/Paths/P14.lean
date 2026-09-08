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
  [opAt 1739 .JUMPDEST,
   pushAt 1740 2 2659,
   opAt 1741 (.Dup ⟨1, by decide⟩),
   opAt 1742 (.Dup ⟨0, by decide⟩),
   opAt 1743 (.Dup ⟨0, by decide⟩),
   pushAt 1744 2 2432,
   opAt 1745 .JUMP]

/-- Instructions 1749..1750, pc 2874..2876: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1746 .JUMPDEST,
   pushAt 1747 1 8]

/-- Instructions 1751..1757, pc 2877..2887: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1748 .JUMPDEST,
   pushAt 1749 2 2673,
   opAt 1750 (.Dup ⟨2, by decide⟩),
   opAt 1751 (.Dup ⟨0, by decide⟩),
   opAt 1752 (.Dup ⟨0, by decide⟩),
   pushAt 1753 2 1939,
   opAt 1754 .JUMP]

/-- Instructions 1758..1764, pc 2888..2897: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1755 .JUMPDEST,
   pushAt 1756 0 0,
   opAt 1757 .NOT,
   opAt 1758 .ADD,
   opAt 1759 (.Dup ⟨0, by decide⟩),
   pushAt 1760 3 2662,
   opAt 1761 .JUMPI]

/-- Instructions 1765..1767, pc 2898..2900: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1762 .POP,
   opAt 1763 .POP,
   opAt 1764 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
