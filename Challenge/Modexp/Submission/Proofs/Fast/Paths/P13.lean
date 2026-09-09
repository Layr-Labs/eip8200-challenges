import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1683..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1683..1723, pc 2333..2473. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1678 .JUMPDEST,
   opAt 1679 (.Dup ⟨0, by decide⟩),
   opAt 1680 .MLOAD,
   opAt 1681 (.Dup ⟨2, by decide⟩),
   opAt 1682 .MLOAD,
   opAt 1683 (.Dup ⟨1, by decide⟩),
   opAt 1684 (.Dup ⟨1, by decide⟩),
   opAt 1685 .GT,
   opAt 1686 (.Swap ⟨1, by decide⟩),
   opAt 1687 .SUB,
   opAt 1688 (.Dup ⟨5, by decide⟩),
   opAt 1689 (.Dup ⟨1, by decide⟩),
   opAt 1690 .SUB,
   opAt 1691 (.Swap ⟨0, by decide⟩),
   opAt 1692 (.Dup ⟨6, by decide⟩),
   opAt 1693 .GT,
   opAt 1694 (.Swap ⟨0, by decide⟩),
   opAt 1695 (.Swap ⟨1, by decide⟩),
   opAt 1696 .OR,
   opAt 1697 (.Swap ⟨4, by decide⟩),
   opAt 1698 .POP,
   opAt 1699 (.Dup ⟨3, by decide⟩),
   opAt 1700 .MSTORE,
   pushAt 1701 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1702 .ADD,
   opAt 1703 (.Swap ⟨0, by decide⟩),
   pushAt 1704 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1705 .ADD,
   opAt 1706 (.Swap ⟨0, by decide⟩),
   opAt 1707 (.Swap ⟨1, by decide⟩),
   pushAt 1708 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1709 .ADD,
   opAt 1710 (.Swap ⟨1, by decide⟩),
   pushAt 1711 2 8224,
   opAt 1712 (.Dup ⟨1, by decide⟩),
   opAt 1713 .GT,
   pushAt 1714 2 2312,
   opAt 1715 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1716 .POP,
   opAt 1717 .POP,
   opAt 1718 .POP,
   opAt 1719 .ISZERO,
   pushAt 1720 2 8224,
   opAt 1721 .MLOAD,
   opAt 1722 .OR,
   pushAt 1723 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1724 .MUL,
   pushAt 1725 2 8256,
   opAt 1726 .ADD,
   pushAt 1727 2 9344,
   opAt 1728 .MLOAD,
   opAt 1729 (.Swap ⟨1, by decide⟩),
   opAt 1730 .MCOPY,
   opAt 1731 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
