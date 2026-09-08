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
  [opAt 1677 .JUMPDEST,
   opAt 1678 (.Dup ⟨0, by decide⟩),
   opAt 1679 .MLOAD,
   opAt 1680 (.Dup ⟨2, by decide⟩),
   opAt 1681 .MLOAD,
   opAt 1682 .JUMPDEST,
   opAt 1683 (.Dup ⟨1, by decide⟩),
   opAt 1684 (.Dup ⟨1, by decide⟩),
   opAt 1685 .GT,
   opAt 1686 (.Swap ⟨1, by decide⟩),
   opAt 1687 .JUMPDEST,
   opAt 1688 .SUB,
   opAt 1689 (.Dup ⟨5, by decide⟩),
   opAt 1690 (.Dup ⟨1, by decide⟩),
   opAt 1691 .SUB,
   opAt 1692 (.Swap ⟨0, by decide⟩),
   opAt 1693 (.Dup ⟨6, by decide⟩),
   opAt 1694 .JUMPDEST,
   opAt 1695 .GT,
   opAt 1696 (.Swap ⟨0, by decide⟩),
   opAt 1697 (.Swap ⟨1, by decide⟩),
   opAt 1698 .OR,
   opAt 1699 (.Swap ⟨4, by decide⟩),
   opAt 1700 .POP,
   opAt 1701 (.Dup ⟨3, by decide⟩),
   opAt 1702 .MSTORE,
   pushAt 1703 1 31, opAt 1704 .NOT,
   opAt 1705 .ADD,
   opAt 1706 (.Swap ⟨0, by decide⟩),
   pushAt 1707 1 31, opAt 1708 .NOT,
   opAt 1709 .ADD,
   opAt 1710 (.Swap ⟨0, by decide⟩),
   opAt 1711 (.Swap ⟨1, by decide⟩),
   pushAt 1712 1 31, opAt 1713 .NOT,
   opAt 1714 .ADD,
   opAt 1715 (.Swap ⟨1, by decide⟩),
   pushAt 1716 2 8224,
   opAt 1717 (.Dup ⟨1, by decide⟩),
   opAt 1718 .GT,
   pushAt 1719 2 2541,
   opAt 1720 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1721 .POP,
   opAt 1722 .POP,
   opAt 1723 .POP,
   opAt 1724 .ISZERO,
   pushAt 1725 2 8224,
   opAt 1726 .MLOAD,
   opAt 1727 .OR,
   pushAt 1728 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1729 .MUL,
   pushAt 1730 2 8256,
   opAt 1731 .ADD,
   pushAt 1732 2 9344,
   opAt 1733 .MLOAD,
   opAt 1734 (.Swap ⟨1, by decide⟩),
   opAt 1735 .MCOPY,
   opAt 1736 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
