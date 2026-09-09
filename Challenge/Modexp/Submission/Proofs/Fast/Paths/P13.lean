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
  [opAt 1680 .JUMPDEST,
   opAt 1681 (.Dup ⟨0, by decide⟩),
   opAt 1682 .MLOAD,
   opAt 1683 (.Dup ⟨2, by decide⟩),
   opAt 1684 .MLOAD,
   opAt 1685 (.Dup ⟨1, by decide⟩),
   opAt 1686 (.Dup ⟨1, by decide⟩),
   opAt 1687 .GT,
   opAt 1688 (.Swap ⟨1, by decide⟩),
   opAt 1689 .SUB,
   opAt 1690 (.Dup ⟨5, by decide⟩),
   opAt 1691 (.Dup ⟨1, by decide⟩),
   opAt 1692 .SUB,
   opAt 1693 (.Swap ⟨0, by decide⟩),
   opAt 1694 (.Dup ⟨6, by decide⟩),
   opAt 1695 .GT,
   opAt 1696 (.Swap ⟨0, by decide⟩),
   opAt 1697 (.Swap ⟨1, by decide⟩),
   opAt 1698 .OR,
   opAt 1699 (.Swap ⟨4, by decide⟩),
   opAt 1700 .POP,
   opAt 1701 (.Dup ⟨3, by decide⟩),
   opAt 1702 .MSTORE,
   pushAt 1703 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1704 .ADD,
   opAt 1705 (.Swap ⟨0, by decide⟩),
   pushAt 1706 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1707 .ADD,
   opAt 1708 (.Swap ⟨0, by decide⟩),
   opAt 1709 (.Swap ⟨1, by decide⟩),
   pushAt 1710 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1711 .ADD,
   opAt 1712 (.Swap ⟨1, by decide⟩),
   pushAt 1713 5 8224,
   opAt 1714 (.Dup ⟨1, by decide⟩),
   opAt 1715 .GT,
   pushAt 1716 2 2328,
   opAt 1717 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1718 .POP,
   opAt 1719 .POP,
   opAt 1720 .POP,
   opAt 1721 .ISZERO,
   pushAt 1722 2 8224,
   opAt 1723 .MLOAD,
   opAt 1724 .OR,
   pushAt 1725 2 1087, opAt 1726 .NOT,
   opAt 1727 .MUL,
   pushAt 1728 2 8256,
   opAt 1729 .ADD,
   pushAt 1730 2 9344,
   opAt 1731 .MLOAD,
   opAt 1732 (.Swap ⟨1, by decide⟩),
   opAt 1733 .MCOPY,
   opAt 1734 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
