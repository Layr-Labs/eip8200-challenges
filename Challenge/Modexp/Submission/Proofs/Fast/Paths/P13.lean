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
  [opAt 1672 .JUMPDEST,
   opAt 1673 (.Dup ⟨0, by decide⟩),
   opAt 1674 .MLOAD,
   opAt 1675 (.Dup ⟨2, by decide⟩),
   opAt 1676 .MLOAD,
   opAt 1677 .JUMPDEST,
   opAt 1678 (.Dup ⟨1, by decide⟩),
   opAt 1679 (.Dup ⟨1, by decide⟩),
   opAt 1680 .GT,
   opAt 1681 (.Swap ⟨1, by decide⟩),
   opAt 1682 .JUMPDEST,
   opAt 1683 .SUB,
   opAt 1684 (.Dup ⟨5, by decide⟩),
   opAt 1685 (.Dup ⟨1, by decide⟩),
   opAt 1686 .SUB,
   opAt 1687 (.Swap ⟨0, by decide⟩),
   opAt 1688 (.Dup ⟨6, by decide⟩),
   opAt 1689 .JUMPDEST,
   opAt 1690 .GT,
   opAt 1691 (.Swap ⟨0, by decide⟩),
   opAt 1692 (.Swap ⟨1, by decide⟩),
   opAt 1693 .OR,
   opAt 1694 (.Swap ⟨4, by decide⟩),
   opAt 1695 .POP,
   opAt 1696 (.Dup ⟨3, by decide⟩),
   opAt 1697 .MSTORE,
   pushAt 1698 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1699 .ADD,
   opAt 1700 (.Swap ⟨0, by decide⟩),
   pushAt 1701 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1702 .ADD,
   opAt 1703 (.Swap ⟨0, by decide⟩),
   opAt 1704 (.Swap ⟨1, by decide⟩),
   pushAt 1705 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1706 .ADD,
   opAt 1707 (.Swap ⟨1, by decide⟩),
   pushAt 1708 2 8224,
   opAt 1709 (.Dup ⟨1, by decide⟩),
   opAt 1710 .GT,
   pushAt 1711 2 2661,
   opAt 1712 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1713 .POP,
   opAt 1714 .POP,
   opAt 1715 .POP,
   opAt 1716 .ISZERO,
   pushAt 1717 2 8224,
   opAt 1718 .MLOAD,
   opAt 1719 .OR,
   pushAt 1720 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1721 .MUL,
   pushAt 1722 2 8256,
   opAt 1723 .ADD,
   pushAt 1724 2 9344,
   opAt 1725 .MLOAD,
   opAt 1726 (.Swap ⟨1, by decide⟩),
   opAt 1727 .MCOPY,
   opAt 1728 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
