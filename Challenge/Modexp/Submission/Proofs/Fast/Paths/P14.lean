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
  [opAt 1736 .JUMPDEST,
   pushAt 1737 2 2507,
   opAt 1738 (.Dup ⟨1, by decide⟩),
   opAt 1739 (.Dup ⟨0, by decide⟩),
   opAt 1740 (.Dup ⟨0, by decide⟩),
   pushAt 1741 2 2219,
   opAt 1742 .JUMP]

/-- Instructions 1749..1750, pc 2874..2514: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1743 .JUMPDEST,
   pushAt 1744 1 8]

/-- Instructions 1751..1757, pc 2515..2525: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1745 .JUMPDEST,
   pushAt 1746 2 2521,
   opAt 1747 (.Dup ⟨2, by decide⟩),
   opAt 1748 (.Dup ⟨0, by decide⟩),
   opAt 1749 (.Dup ⟨0, by decide⟩),
   pushAt 1750 2 4465,
   opAt 1751 .JUMP]

/-- Instructions 1758..1764, pc 2526..2535: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1752 .JUMPDEST,
   pushAt 1753 0 0,
   opAt 1754 .NOT,
   opAt 1755 .ADD,
   opAt 1756 (.Dup ⟨0, by decide⟩),
   pushAt 1757 3 2510,
   opAt 1758 .JUMPI]

/-- Instructions 1765..1767, pc 2536..2900: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1759 .POP,
   opAt 1760 .POP,
   opAt 1761 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
