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
  [opAt 1673 .JUMPDEST,
   opAt 1674 (.Dup ⟨0, by decide⟩),
   opAt 1675 .MLOAD,
   opAt 1676 (.Dup ⟨2, by decide⟩),
   opAt 1677 .MLOAD,
   opAt 1678 (.Dup ⟨1, by decide⟩),
   opAt 1679 (.Dup ⟨1, by decide⟩),
   opAt 1680 .GT,
   opAt 1681 (.Swap ⟨1, by decide⟩),
   opAt 1682 .SUB,
   opAt 1683 (.Dup ⟨5, by decide⟩),
   opAt 1684 (.Dup ⟨1, by decide⟩),
   opAt 1685 .SUB,
   opAt 1686 (.Swap ⟨0, by decide⟩),
   opAt 1687 (.Dup ⟨6, by decide⟩),
   opAt 1688 .GT,
   opAt 1689 (.Swap ⟨0, by decide⟩),
   opAt 1690 (.Swap ⟨1, by decide⟩),
   opAt 1691 .OR,
   opAt 1692 (.Swap ⟨4, by decide⟩),
   opAt 1693 .POP,
   opAt 1694 (.Dup ⟨3, by decide⟩),
   opAt 1695 .MSTORE,
   pushAt 1696 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1697 .ADD,
   opAt 1698 (.Swap ⟨0, by decide⟩),
   pushAt 1699 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1700 .ADD,
   opAt 1701 (.Swap ⟨0, by decide⟩),
   opAt 1702 (.Swap ⟨1, by decide⟩),
   pushAt 1703 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1704 .ADD,
   opAt 1705 (.Swap ⟨1, by decide⟩),
   pushAt 1706 2 8224,
   opAt 1707 (.Dup ⟨1, by decide⟩),
   opAt 1708 .GT,
   pushAt 1709 2 2323,
   opAt 1710 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1711 .POP,
   opAt 1712 .POP,
   opAt 1713 .POP,
   opAt 1714 .ISZERO,
   pushAt 1715 2 8224,
   opAt 1716 .MLOAD,
   opAt 1717 .OR,
   pushAt 1718 2 1087, opAt 1719 .NOT,
   opAt 1720 .MUL,
   pushAt 1721 2 8256,
   opAt 1722 .ADD,
   pushAt 1723 2 9344,
   opAt 1724 .MLOAD,
   opAt 1725 (.Swap ⟨1, by decide⟩),
   opAt 1726 .MCOPY,
   opAt 1727 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
