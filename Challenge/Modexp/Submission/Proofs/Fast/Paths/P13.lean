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
  [opAt 1665 .JUMPDEST,
   opAt 1666 (.Dup ⟨0, by decide⟩),
   opAt 1667 .MLOAD,
   pushAt 1668 32 115792089237316195423570985008687907853269984665640564039457584007913129631680,
   opAt 1669 (.Dup ⟨2, by decide⟩),
   opAt 1670 .ADD,
   opAt 1671 .MLOAD,
   opAt 1672 (.Dup ⟨1, by decide⟩),
   opAt 1673 (.Dup ⟨1, by decide⟩),
   opAt 1674 .GT,
   opAt 1675 (.Swap ⟨1, by decide⟩),
   opAt 1676 .SUB,
   opAt 1677 (.Dup ⟨3, by decide⟩),
   opAt 1678 (.Dup ⟨1, by decide⟩),
   opAt 1679 .SUB,
   opAt 1680 (.Swap ⟨0, by decide⟩),
   opAt 1681 (.Dup ⟨4, by decide⟩),
   opAt 1682 .GT,
   opAt 1683 (.Swap ⟨0, by decide⟩),
   opAt 1684 (.Swap ⟨1, by decide⟩),
   opAt 1685 .OR,
   opAt 1686 (.Swap ⟨2, by decide⟩),
   opAt 1687 .POP,
   pushAt 1688 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1689 (.Dup ⟨2, by decide⟩),
   opAt 1690 .ADD,
   opAt 1691 .MSTORE,
   pushAt 1692 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1693 .ADD,
   pushAt 1694 2 8224,
   opAt 1695 (.Dup ⟨1, by decide⟩),
   opAt 1696 .GT,
   pushAt 1697 2 2317,
   opAt 1698 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1699 .POP,
   opAt 1700 .ISZERO,
   pushAt 1701 2 8224,
   opAt 1702 .MLOAD,
   opAt 1703 .OR,
   pushAt 1704 2 1087, opAt 1705 .NOT,
   opAt 1706 .MUL,
   pushAt 1707 2 8256,
   opAt 1708 .ADD,
   pushAt 1709 2 9344,
   opAt 1710 .MLOAD,
   opAt 1711 (.Swap ⟨1, by decide⟩),
   opAt 1712 .MCOPY,
   opAt 1713 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
