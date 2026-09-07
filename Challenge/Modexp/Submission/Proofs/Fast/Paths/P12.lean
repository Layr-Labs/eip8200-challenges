import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (original instructions 1627..1682;
relocated indices 1652..1707). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1627`, now instructions 1652..1686, pc 2529..2663. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1652 .JUMPDEST,
   opAt 1653 (.Dup ⟨1, by decide⟩),
   opAt 1654 .MLOAD,
   opAt 1655 (.Dup ⟨3, by decide⟩),
   opAt 1656 .MLOAD,
   opAt 1657 (.Dup ⟨1, by decide⟩),
   opAt 1658 .ADD,
   opAt 1659 (.Swap ⟨0, by decide⟩),
   opAt 1660 (.Dup ⟨1, by decide⟩),
   opAt 1661 .LT,
   opAt 1662 (.Swap ⟨0, by decide⟩),
   opAt 1663 (.Dup ⟨5, by decide⟩),
   opAt 1664 .ADD,
   opAt 1665 (.Swap ⟨4, by decide⟩),
   opAt 1666 (.Dup ⟨5, by decide⟩),
   opAt 1667 .LT,
   opAt 1668 .OR,
   opAt 1669 (.Swap ⟨3, by decide⟩),
   opAt 1670 (.Dup ⟨1, by decide⟩),
   opAt 1671 .MSTORE,
   pushAt 1672 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1673 .ADD,
   opAt 1674 (.Swap ⟨0, by decide⟩),
   pushAt 1675 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1676 .ADD,
   opAt 1677 (.Swap ⟨0, by decide⟩),
   opAt 1678 (.Swap ⟨1, by decide⟩),
   pushAt 1679 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1680 .ADD,
   opAt 1681 (.Swap ⟨1, by decide⟩),
   pushAt 1682 2 8224,
   opAt 1683 (.Dup ⟨1, by decide⟩),
   opAt 1684 .GT,
   pushAt 1685 2 2529,
   opAt 1686 .JUMPI]

/-- Original block `1662`, now instructions 1687..1691, pc 2664..2670. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1687 .POP,
   opAt 1688 .POP,
   opAt 1689 .POP,
   pushAt 1690 2 8224,
   opAt 1691 .MSTORE]

/-- Original block `1667`, now instructions 1692..1707, pc 2671..2694. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1692 .JUMPDEST,
   pushAt 1693 2 9440,
   opAt 1694 .MLOAD,
   pushAt 1695 2 9408,
   opAt 1696 .MLOAD,
   opAt 1697 (.Dup ⟨1, by decide⟩),
   pushAt 1698 2 7168,
   opAt 1699 .ADD,
   pushAt 1700 2 8256,
   opAt 1701 (.Swap ⟨0, by decide⟩),
   opAt 1702 .SUB,
   pushAt 1703 0 0,
   opAt 1704 (.Swap ⟨2, by decide⟩),
   opAt 1705 (.Swap ⟨0, by decide⟩),
   opAt 1706 (.Swap ⟨1, by decide⟩),
   opAt 1707 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
