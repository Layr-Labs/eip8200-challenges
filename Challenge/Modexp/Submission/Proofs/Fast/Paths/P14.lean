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
  [
   pushAt 1726 2 2488,
   opAt 1727 (.Dup ⟨1, by decide⟩),
   opAt 1728 (.Dup ⟨0, by decide⟩),
   opAt 1729 (.Dup ⟨0, by decide⟩),
   pushAt 1730 2 2209,
   opAt 1731 .JUMP]

/-- Instructions 1749..1750, pc 2874..2514: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1732 .JUMPDEST,
   pushAt 1733 1 8]

/-- Instructions 1751..1757, pc 2515..2525: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1734 .JUMPDEST,
   pushAt 1735 2 2502,
   opAt 1736 (.Dup ⟨2, by decide⟩),
   opAt 1737 (.Dup ⟨0, by decide⟩),
   opAt 1738 (.Dup ⟨0, by decide⟩),
   pushAt 1739 2 4432,
   opAt 1740 .JUMP]

/-- Instructions 1758..1764, pc 2526..2535: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1741 .JUMPDEST,
   pushAt 1742 0 0,
   opAt 1743 .NOT,
   opAt 1744 .ADD,
   opAt 1745 (.Dup ⟨0, by decide⟩),
   pushAt 1746 3 2491,
   opAt 1747 .JUMPI]

/-- Instructions 1765..1767, pc 2536..2900: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1748 .POP,
   opAt 1749 .POP,
   opAt 1750 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
