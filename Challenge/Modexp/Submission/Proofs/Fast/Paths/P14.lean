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
  [opAt 1735 .JUMPDEST,
   pushAt 1736 2 2488,
   opAt 1737 (.Dup ⟨1, by decide⟩),
   opAt 1738 (.Dup ⟨0, by decide⟩),
   opAt 1739 (.Dup ⟨0, by decide⟩),
   pushAt 1740 2 2203,
   opAt 1741 .JUMP]

/-- Instructions 1749..1750, pc 2874..2514: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1742 .JUMPDEST,
   pushAt 1743 1 8]

/-- Instructions 1751..1757, pc 2515..2525: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1744 .JUMPDEST,
   pushAt 1745 2 2502,
   opAt 1746 (.Dup ⟨2, by decide⟩),
   opAt 1747 (.Dup ⟨0, by decide⟩),
   opAt 1748 (.Dup ⟨0, by decide⟩),
   pushAt 1749 2 4428,
   opAt 1750 .JUMP]

/-- Instructions 1758..1764, pc 2526..2535: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1751 .JUMPDEST,
   pushAt 1752 0 0,
   opAt 1753 .NOT,
   opAt 1754 .ADD,
   opAt 1755 (.Dup ⟨0, by decide⟩),
   pushAt 1756 2 2491,
   opAt 1757 .JUMPI]

/-- Instructions 1765..1767, pc 2536..2900: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1758 .POP,
   opAt 1759 .POP,
   opAt 1760 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
