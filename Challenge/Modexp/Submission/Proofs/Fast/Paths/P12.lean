import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (original instructions 1627..1682;
relocated indices 1658..1713). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1627`, now instructions 1658..1692, pc 2544..2678. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1658 .JUMPDEST,
   opAt 1659 (.Dup ⟨1, by decide⟩),
   opAt 1660 .MLOAD,
   opAt 1661 (.Dup ⟨3, by decide⟩),
   opAt 1662 .MLOAD,
   opAt 1663 (.Dup ⟨1, by decide⟩),
   opAt 1664 .ADD,
   opAt 1665 (.Swap ⟨0, by decide⟩),
   opAt 1666 (.Dup ⟨1, by decide⟩),
   opAt 1667 .LT,
   opAt 1668 (.Swap ⟨0, by decide⟩),
   opAt 1669 (.Dup ⟨5, by decide⟩),
   opAt 1670 .ADD,
   opAt 1671 (.Swap ⟨4, by decide⟩),
   opAt 1672 (.Dup ⟨5, by decide⟩),
   opAt 1673 .LT,
   opAt 1674 .OR,
   opAt 1675 (.Swap ⟨3, by decide⟩),
   opAt 1676 (.Dup ⟨1, by decide⟩),
   opAt 1677 .MSTORE,
   pushAt 1678 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1679 .ADD,
   opAt 1680 (.Swap ⟨0, by decide⟩),
   pushAt 1681 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1682 .ADD,
   opAt 1683 (.Swap ⟨0, by decide⟩),
   opAt 1684 (.Swap ⟨1, by decide⟩),
   pushAt 1685 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1686 .ADD,
   opAt 1687 (.Swap ⟨1, by decide⟩),
   pushAt 1688 2 8224,
   opAt 1689 (.Dup ⟨1, by decide⟩),
   opAt 1690 .GT,
   pushAt 1691 2 2544,
   opAt 1692 .JUMPI]

/-- Original block `1662`, now instructions 1693..1697, pc 2679..2685. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1693 .POP,
   opAt 1694 .POP,
   opAt 1695 .POP,
   pushAt 1696 2 8224,
   opAt 1697 .MSTORE]

/-- Original block `1667`, now instructions 1698..1713, pc 2686..2709. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1698 .JUMPDEST,
   pushAt 1699 2 9440,
   opAt 1700 .MLOAD,
   pushAt 1701 2 9408,
   opAt 1702 .MLOAD,
   opAt 1703 (.Dup ⟨1, by decide⟩),
   pushAt 1704 2 7168,
   opAt 1705 .ADD,
   pushAt 1706 2 8256,
   opAt 1707 (.Swap ⟨0, by decide⟩),
   opAt 1708 .SUB,
   pushAt 1709 0 0,
   opAt 1710 (.Swap ⟨2, by decide⟩),
   opAt 1711 (.Swap ⟨0, by decide⟩),
   opAt 1712 (.Swap ⟨1, by decide⟩),
   opAt 1713 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
