import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1742..1757, pc 2863..2887: test for a nonempty exponent
whose first byte is exactly one. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1742 .JUMPDEST,
   opAt 1743 (.Dup ⟨3, by decide⟩),
   opAt 1744 .ISZERO,
   pushAt 1745 2 1756,
   opAt 1746 .JUMPI,
   pushAt 1747 2 9472,
   opAt 1748 .MLOAD,
   opAt 1749 .CALLDATALOAD,
   pushAt 1750 0 0,
   opAt 1751 .BYTE,
   pushAt 1752 1 1,
   opAt 1753 .EQ,
   pushAt 1754 2 2888,
   opAt 1755 .JUMPI,
   pushAt 1756 2 1756,
   opAt 1757 .JUMP]

/-- Taken prefix of `blk1742` for the empty-exponent branch. -/
def blk1742empty :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1742 .JUMPDEST,
   opAt 1743 (.Dup ⟨3, by decide⟩),
   opAt 1744 .ISZERO,
   pushAt 1745 2 1756,
   opAt 1746 .JUMPI]

/-- Taken prefix of `blk1742` for the first-byte-is-one branch. -/
def blk1742one :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1742 .JUMPDEST,
   opAt 1743 (.Dup ⟨3, by decide⟩),
   opAt 1744 .ISZERO,
   pushAt 1745 2 1756,
   opAt 1746 .JUMPI,
   pushAt 1747 2 9472,
   opAt 1748 .MLOAD,
   opAt 1749 .CALLDATALOAD,
   pushAt 1750 0 0,
   opAt 1751 .BYTE,
   pushAt 1752 1 1,
   opAt 1753 .EQ,
   pushAt 1754 2 2888,
   opAt 1755 .JUMPI]

/-- Instructions 1758..1766, pc 2888..2905: copy `BASE` to `ACC` and
continue at exponent byte one. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1758 .JUMPDEST,
   pushAt 1759 2 9344,
   opAt 1760 .MLOAD,
   pushAt 1761 2 2048,
   pushAt 1762 2 1024,
   opAt 1763 .MCOPY,
   pushAt 1764 1 1,
   pushAt 1765 2 1769,
   opAt 1766 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
