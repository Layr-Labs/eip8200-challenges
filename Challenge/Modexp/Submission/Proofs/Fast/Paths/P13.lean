import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1683..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1683..1723, pc 2666..2806. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1673 .JUMPDEST,
   opAt 1674 (.Dup ⟨0, by decide⟩),
   opAt 1675 .MLOAD,
   opAt 1676 (.Dup ⟨2, by decide⟩),
   opAt 1677 .MLOAD,
   opAt 1678 .JUMPDEST,
   opAt 1679 (.Dup ⟨1, by decide⟩),
   opAt 1680 (.Dup ⟨1, by decide⟩),
   opAt 1681 .GT,
   opAt 1682 (.Swap ⟨1, by decide⟩),
   opAt 1683 .JUMPDEST,
   opAt 1684 .SUB,
   opAt 1685 (.Dup ⟨5, by decide⟩),
   opAt 1686 (.Dup ⟨1, by decide⟩),
   opAt 1687 .SUB,
   opAt 1688 (.Swap ⟨0, by decide⟩),
   opAt 1689 (.Dup ⟨6, by decide⟩),
   opAt 1690 .JUMPDEST,
   opAt 1691 .GT,
   opAt 1692 (.Swap ⟨0, by decide⟩),
   opAt 1693 (.Swap ⟨1, by decide⟩),
   opAt 1694 .OR,
   opAt 1695 (.Swap ⟨4, by decide⟩),
   opAt 1696 .POP,
   opAt 1697 (.Dup ⟨3, by decide⟩),
   opAt 1698 .MSTORE,
   pushAt 1699 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1700 .ADD,
   opAt 1701 (.Swap ⟨0, by decide⟩),
   pushAt 1702 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1703 .ADD,
   opAt 1704 (.Swap ⟨0, by decide⟩),
   opAt 1705 (.Swap ⟨1, by decide⟩),
   pushAt 1706 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1707 .ADD,
   opAt 1708 (.Swap ⟨1, by decide⟩),
   pushAt 1709 2 8224,
   opAt 1710 (.Dup ⟨1, by decide⟩),
   opAt 1711 .GT,
   pushAt 1712 2 2661,
   opAt 1713 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1714 .POP,
   opAt 1715 .POP,
   opAt 1716 .POP,
   opAt 1717 .ISZERO,
   pushAt 1718 2 8224,
   opAt 1719 .MLOAD,
   opAt 1720 .OR,
   pushAt 1721 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1722 .MUL,
   pushAt 1723 2 8256,
   opAt 1724 .ADD,
   pushAt 1725 2 9344,
   opAt 1726 .MLOAD,
   opAt 1727 (.Swap ⟨1, by decide⟩),
   opAt 1728 .MCOPY,
   opAt 1729 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
