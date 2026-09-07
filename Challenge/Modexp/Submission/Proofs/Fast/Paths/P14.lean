import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1773..1798).

`CCB` (pc 2907) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1742`, now instructions 1773..1779, pc 2907..2917: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1773 .JUMPDEST,
   pushAt 1774 2 2918,
   opAt 1775 (.Dup ⟨1, by decide⟩),
   opAt 1776 (.Dup ⟨0, by decide⟩),
   opAt 1777 (.Dup ⟨0, by decide⟩),
   pushAt 1778 2 2511,
   opAt 1779 .JUMP]

/-- Original block `1749`, now instructions 1780..1781, pc 2918..2919: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1780 .JUMPDEST,
   pushAt 1781 1 8]

/-- Original block `1751`, now instructions 1782..1788, pc 2921..2931: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1782 .JUMPDEST,
   pushAt 1783 2 2932,
   opAt 1784 (.Dup ⟨2, by decide⟩),
   opAt 1785 (.Dup ⟨0, by decide⟩),
   opAt 1786 (.Dup ⟨0, by decide⟩),
   pushAt 1787 2 1939,
   opAt 1788 .JUMP]

/-- Original block `1758`, now instructions 1789..1795, pc 2932..2941: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1789 .JUMPDEST,
   pushAt 1790 0 0,
   opAt 1791 .NOT,
   opAt 1792 .ADD,
   opAt 1793 (.Dup ⟨0, by decide⟩),
   pushAt 1794 3 2921,
   opAt 1795 .JUMPI]

/-- Original block `1765`, now instructions 1796..1798, pc 2942..2944: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1796 .POP,
   opAt 1797 .POP,
   opAt 1798 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
