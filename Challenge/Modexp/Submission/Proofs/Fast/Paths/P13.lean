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
  [opAt 1652 .JUMPDEST,
   opAt 1653 (.Dup ⟨0, by decide⟩),
   opAt 1654 .MLOAD,
   pushAt 1655 32 115792089237316195423570985008687907853269984665640564039457584007913129631680,
   opAt 1656 (.Dup ⟨2, by decide⟩),
   opAt 1657 .ADD,
   opAt 1658 .MLOAD,
   opAt 1659 (.Dup ⟨1, by decide⟩),
   opAt 1660 (.Dup ⟨1, by decide⟩),
   opAt 1661 .GT,
   opAt 1662 (.Swap ⟨1, by decide⟩),
   opAt 1663 .SUB,
   opAt 1664 (.Dup ⟨3, by decide⟩),
   opAt 1665 (.Dup ⟨1, by decide⟩),
   opAt 1666 .SUB,
   opAt 1667 (.Swap ⟨0, by decide⟩),
   opAt 1668 (.Dup ⟨4, by decide⟩),
   opAt 1669 .GT,
   opAt 1670 (.Swap ⟨0, by decide⟩),
   opAt 1671 (.Swap ⟨1, by decide⟩),
   opAt 1672 .OR,
   opAt 1673 (.Swap ⟨2, by decide⟩),
   opAt 1674 .POP,
   pushAt 1675 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1676 (.Dup ⟨2, by decide⟩),
   opAt 1677 .ADD,
   opAt 1678 .MSTORE,
   pushAt 1679 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1680 .ADD,
   pushAt 1681 2 8224,
   opAt 1682 (.Dup ⟨1, by decide⟩),
   opAt 1683 .GT,
   pushAt 1684 2 2311,
   opAt 1685 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1686 .POP,
   opAt 1687 .ISZERO,
   pushAt 1688 2 8224,
   opAt 1689 .MLOAD,
   opAt 1690 .OR,
   pushAt 1691 2 1087, opAt 1692 .NOT,
   opAt 1693 .MUL,
   pushAt 1694 2 8256,
   opAt 1695 .ADD,
   pushAt 1696 2 9344,
   opAt 1697 .MLOAD,
   opAt 1698 (.Swap ⟨1, by decide⟩),
   opAt 1699 .MCOPY,
   opAt 1700 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
