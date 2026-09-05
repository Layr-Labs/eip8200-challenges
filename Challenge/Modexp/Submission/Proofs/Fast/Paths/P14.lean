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
  [opAt 1743 .JUMPDEST,
   pushAt 1744 2 2995,
   opAt 1745 (.Dup ⟨1, by decide⟩),
   opAt 1746 (.Dup ⟨0, by decide⟩),
   opAt 1747 (.Dup ⟨0, by decide⟩),
   pushAt 1748 2 2467,
   opAt 1749 .JUMP]

/-- Instructions 1749..1750, pc 2874..2876: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1750 .JUMPDEST,
   pushAt 1751 1 8]

/-- Instructions 1751..1757, pc 2877..2887: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1752 .JUMPDEST,
   pushAt 1753 2 2888,
   opAt 1754 (.Dup ⟨2, by decide⟩),
   opAt 1755 (.Dup ⟨0, by decide⟩),
   opAt 1756 (.Dup ⟨0, by decide⟩),
   pushAt 1757 2 1939,
   opAt 1758 .JUMP]

/-- Instructions 1758..1764, pc 2888..2897: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1759 .JUMPDEST,
   pushAt 1760 1 1,
   opAt 1761 (.Swap ⟨0, by decide⟩),
   opAt 1762 .SUB,
   opAt 1763 (.Dup ⟨0, by decide⟩),
   pushAt 1764 2 2877,
   opAt 1765 .JUMPI]

/-- Instructions 1765..1767, pc 2898..2900: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1766 .POP,
   opAt 1767 .POP,
   opAt 1768 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
