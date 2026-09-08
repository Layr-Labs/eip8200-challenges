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
  [opAt 1705 .JUMPDEST,
   pushAt 1706 2 2723,
   opAt 1707 (.Dup ⟨1, by decide⟩),
   opAt 1708 (.Dup ⟨0, by decide⟩),
   opAt 1709 (.Dup ⟨0, by decide⟩),
   pushAt 1710 2 2324,
   opAt 1711 .JUMP]

/-- Instructions 1749..1750, pc 2874..2876: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1712 .JUMPDEST,
   pushAt 1713 1 8]

/-- Instructions 1751..1757, pc 2877..2887: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1714 .JUMPDEST,
   pushAt 1715 2 2737,
   opAt 1716 (.Dup ⟨2, by decide⟩),
   opAt 1717 (.Dup ⟨0, by decide⟩),
   opAt 1718 (.Dup ⟨0, by decide⟩),
   pushAt 1719 2 1908,
   opAt 1720 .JUMP]

/-- Instructions 1758..1764, pc 2888..2897: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1721 .JUMPDEST,
   pushAt 1722 0 0,
   opAt 1723 .NOT,
   opAt 1724 .ADD,
   opAt 1725 (.Dup ⟨0, by decide⟩),
   pushAt 1726 3 2726,
   opAt 1727 .JUMPI]

/-- Instructions 1765..1767, pc 2898..2900: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1728 .POP,
   opAt 1729 .POP,
   opAt 1730 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
