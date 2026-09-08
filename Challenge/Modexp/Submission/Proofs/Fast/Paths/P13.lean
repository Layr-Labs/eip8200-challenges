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
  [opAt 1678 .JUMPDEST,
   opAt 1679 (.Dup ⟨0, by decide⟩),
   opAt 1680 .MLOAD,
   opAt 1681 (.Dup ⟨2, by decide⟩),
   opAt 1682 .MLOAD,
   opAt 1683 .JUMPDEST,
   opAt 1684 (.Dup ⟨1, by decide⟩),
   opAt 1685 (.Dup ⟨1, by decide⟩),
   opAt 1686 .GT,
   opAt 1687 (.Swap ⟨1, by decide⟩),
   opAt 1688 .JUMPDEST,
   opAt 1689 .SUB,
   opAt 1690 (.Dup ⟨5, by decide⟩),
   opAt 1691 (.Dup ⟨1, by decide⟩),
   opAt 1692 .SUB,
   opAt 1693 (.Swap ⟨0, by decide⟩),
   opAt 1694 (.Dup ⟨6, by decide⟩),
   opAt 1695 .JUMPDEST,
   opAt 1696 .GT,
   opAt 1697 (.Swap ⟨0, by decide⟩),
   opAt 1698 (.Swap ⟨1, by decide⟩),
   opAt 1699 .OR,
   opAt 1700 (.Swap ⟨4, by decide⟩),
   opAt 1701 .POP,
   opAt 1702 (.Dup ⟨3, by decide⟩),
   opAt 1703 .MSTORE,
   pushAt 1704 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1705 .ADD,
   opAt 1706 (.Swap ⟨0, by decide⟩),
   pushAt 1707 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1708 .ADD,
   opAt 1709 (.Swap ⟨0, by decide⟩),
   opAt 1710 (.Swap ⟨1, by decide⟩),
   pushAt 1711 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1712 .ADD,
   opAt 1713 (.Swap ⟨1, by decide⟩),
   pushAt 1714 2 8224,
   opAt 1715 (.Dup ⟨1, by decide⟩),
   opAt 1716 .GT,
   pushAt 1717 2 2662,
   opAt 1718 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1719 .POP,
   opAt 1720 .POP,
   opAt 1721 .POP,
   opAt 1722 .ISZERO,
   pushAt 1723 2 8224,
   opAt 1724 .MLOAD,
   opAt 1725 .OR,
   pushAt 1726 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1727 .MUL,
   pushAt 1728 2 8256,
   opAt 1729 .ADD,
   pushAt 1730 2 9344,
   opAt 1731 .MLOAD,
   opAt 1732 (.Swap ⟨1, by decide⟩),
   opAt 1733 .MCOPY,
   opAt 1734 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
