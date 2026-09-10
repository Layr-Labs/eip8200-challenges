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
  [pushAt 1701 2 2478,
   opAt 1702 (.Dup ⟨1, by decide⟩),
   opAt 1703 (.Dup ⟨0, by decide⟩),
   opAt 1704 (.Dup ⟨0, by decide⟩),
   pushAt 1705 2 2199,
   opAt 1706 .JUMP]

/-- Instructions 1749..1750, pc 2874..2514: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1707 .JUMPDEST,
   pushAt 1708 1 8]

/-- Instructions 1751..1757, pc 2515..2525: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1709 .JUMPDEST,
   pushAt 1710 2 2492,
   opAt 1711 (.Dup ⟨2, by decide⟩),
   opAt 1712 (.Dup ⟨0, by decide⟩),
   opAt 1713 (.Dup ⟨0, by decide⟩),
   pushAt 1714 2 4428,
   opAt 1715 .JUMP]

/-- Instructions 1758..1764, pc 2526..2535: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1716 .JUMPDEST,
   pushAt 1717 0 0,
   opAt 1718 .NOT,
   opAt 1719 .ADD,
   opAt 1720 (.Dup ⟨0, by decide⟩),
   pushAt 1721 3 2481,
   opAt 1722 .JUMPI]

/-- Instructions 1765..1767, pc 2536..2900: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1723 .POP,
   opAt 1724 .POP,
   opAt 1725 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
