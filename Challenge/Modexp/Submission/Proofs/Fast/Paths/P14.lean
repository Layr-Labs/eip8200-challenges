import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1767..1792).

`CCB` (pc 2892) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1742`, now instructions 1767..1773, pc 2892..2902: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1767 .JUMPDEST,
   pushAt 1768 2 2903,
   opAt 1769 (.Dup ⟨1, by decide⟩),
   opAt 1770 (.Dup ⟨0, by decide⟩),
   opAt 1771 (.Dup ⟨0, by decide⟩),
   pushAt 1772 2 2496,
   opAt 1773 .JUMP]

/-- Original block `1749`, now instructions 1774..1775, pc 2903..2905: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1774 .JUMPDEST,
   pushAt 1775 1 8]

/-- Original block `1751`, now instructions 1776..1782, pc 2906..2916: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1776 .JUMPDEST,
   pushAt 1777 2 2917,
   opAt 1778 (.Dup ⟨2, by decide⟩),
   opAt 1779 (.Dup ⟨0, by decide⟩),
   opAt 1780 (.Dup ⟨0, by decide⟩),
   pushAt 1781 2 1939,
   opAt 1782 .JUMP]

/-- Original block `1758`, now instructions 1783..1789, pc 2917..2926: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1783 .JUMPDEST,
   pushAt 1784 0 0,
   opAt 1785 .NOT,
   opAt 1786 .ADD,
   opAt 1787 (.Dup ⟨0, by decide⟩),
   pushAt 1788 3 2906,
   opAt 1789 .JUMPI]

/-- Original block `1765`, now instructions 1790..1792, pc 2927..2929: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1790 .POP,
   opAt 1791 .POP,
   opAt 1792 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
