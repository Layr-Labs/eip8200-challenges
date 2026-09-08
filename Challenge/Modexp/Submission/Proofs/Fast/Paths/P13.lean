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
  [opAt 1662 .JUMPDEST,
   opAt 1663 (.Dup ⟨0, by decide⟩),
   opAt 1664 .MLOAD,
   opAt 1665 (.Dup ⟨2, by decide⟩),
   opAt 1666 .MLOAD,
      opAt 1667 (.Dup ⟨1, by decide⟩),
   opAt 1668 (.Dup ⟨1, by decide⟩),
   opAt 1669 .GT,
   opAt 1670 (.Swap ⟨1, by decide⟩),
      opAt 1671 .SUB,
   opAt 1672 (.Dup ⟨5, by decide⟩),
   opAt 1673 (.Dup ⟨1, by decide⟩),
   opAt 1674 .SUB,
   opAt 1675 (.Swap ⟨0, by decide⟩),
   opAt 1676 (.Dup ⟨6, by decide⟩),
      opAt 1677 .GT,
   opAt 1678 (.Swap ⟨0, by decide⟩),
   opAt 1679 (.Swap ⟨1, by decide⟩),
   opAt 1680 .OR,
   opAt 1681 (.Swap ⟨4, by decide⟩),
   opAt 1682 .POP,
   opAt 1683 (.Dup ⟨3, by decide⟩),
   opAt 1684 .MSTORE,
   pushAt 1685 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1686 .ADD,
   opAt 1687 (.Swap ⟨0, by decide⟩),
   pushAt 1688 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1689 .ADD,
   opAt 1690 (.Swap ⟨0, by decide⟩),
   opAt 1691 (.Swap ⟨1, by decide⟩),
   pushAt 1692 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1693 .ADD,
   opAt 1694 (.Swap ⟨1, by decide⟩),
   pushAt 1695 2 8224,
   opAt 1696 (.Dup ⟨1, by decide⟩),
   opAt 1697 .GT,
   pushAt 1698 2 2633,
   opAt 1699 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1700 .POP,
   opAt 1701 .POP,
   opAt 1702 .POP,
   opAt 1703 .ISZERO,
   pushAt 1704 2 8224,
   opAt 1705 .MLOAD,
   opAt 1706 .OR,
   pushAt 1707 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1708 .MUL,
   pushAt 1709 2 8256,
   opAt 1710 .ADD,
   pushAt 1711 2 9344,
   opAt 1712 .MLOAD,
   opAt 1713 (.Swap ⟨1, by decide⟩),
   opAt 1714 .MCOPY,
   opAt 1715 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
