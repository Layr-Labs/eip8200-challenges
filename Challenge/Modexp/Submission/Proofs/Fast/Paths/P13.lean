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
  [opAt 1676 .JUMPDEST,
   opAt 1677 (.Dup ⟨0, by decide⟩),
   opAt 1678 .MLOAD,
   opAt 1679 (.Dup ⟨2, by decide⟩),
   opAt 1680 .MLOAD,
   opAt 1681 .JUMPDEST,
   opAt 1682 (.Dup ⟨1, by decide⟩),
   opAt 1683 (.Dup ⟨1, by decide⟩),
   opAt 1684 .GT,
   opAt 1685 (.Swap ⟨1, by decide⟩),
   opAt 1686 .JUMPDEST,
   opAt 1687 .SUB,
   opAt 1688 (.Dup ⟨5, by decide⟩),
   opAt 1689 (.Dup ⟨1, by decide⟩),
   opAt 1690 .SUB,
   opAt 1691 (.Swap ⟨0, by decide⟩),
   opAt 1692 (.Dup ⟨6, by decide⟩),
   opAt 1693 .JUMPDEST,
   opAt 1694 .GT,
   opAt 1695 (.Swap ⟨0, by decide⟩),
   opAt 1696 (.Swap ⟨1, by decide⟩),
   opAt 1697 .OR,
   opAt 1698 (.Swap ⟨4, by decide⟩),
   opAt 1699 .POP,
   opAt 1700 (.Dup ⟨3, by decide⟩),
   opAt 1701 .MSTORE,
   pushAt 1702 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1703 .ADD,
   opAt 1704 (.Swap ⟨0, by decide⟩),
   pushAt 1705 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1706 .ADD,
   opAt 1707 (.Swap ⟨0, by decide⟩),
   opAt 1708 (.Swap ⟨1, by decide⟩),
   pushAt 1709 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1710 .ADD,
   opAt 1711 (.Swap ⟨1, by decide⟩),
   pushAt 1712 2 8224,
   opAt 1713 (.Dup ⟨1, by decide⟩),
   opAt 1714 .GT,
   pushAt 1715 2 2328,
   opAt 1716 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1717 .POP,
   opAt 1718 .POP,
   opAt 1719 .POP,
   opAt 1720 .ISZERO,
   pushAt 1721 2 8224,
   opAt 1722 .MLOAD,
   opAt 1723 .OR,
   pushAt 1724 2 1087, opAt 1725 .NOT,
   opAt 1726 .MUL,
   pushAt 1727 2 8256,
   opAt 1728 .ADD,
   pushAt 1729 2 9344,
   opAt 1730 .MLOAD,
   opAt 1731 (.Swap ⟨1, by decide⟩),
   opAt 1732 .MCOPY,
   opAt 1733 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
