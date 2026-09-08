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
  [opAt 1671 .JUMPDEST,
   opAt 1672 (.Dup ⟨0, by decide⟩),
   opAt 1673 .MLOAD,
   opAt 1674 (.Dup ⟨2, by decide⟩),
   opAt 1675 .MLOAD,
      opAt 1676 (.Dup ⟨1, by decide⟩),
   opAt 1677 (.Dup ⟨1, by decide⟩),
   opAt 1678 .GT,
   opAt 1679 (.Swap ⟨1, by decide⟩),
      opAt 1680 .SUB,
   opAt 1681 (.Dup ⟨5, by decide⟩),
   opAt 1682 (.Dup ⟨1, by decide⟩),
   opAt 1683 .SUB,
   opAt 1684 (.Swap ⟨0, by decide⟩),
   opAt 1685 (.Dup ⟨6, by decide⟩),
      opAt 1686 .GT,
   opAt 1687 (.Swap ⟨0, by decide⟩),
   opAt 1688 (.Swap ⟨1, by decide⟩),
   opAt 1689 .OR,
   opAt 1690 (.Swap ⟨4, by decide⟩),
   opAt 1691 .POP,
   opAt 1692 (.Dup ⟨3, by decide⟩),
   opAt 1693 .MSTORE,
   pushAt 1694 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1695 .ADD,
   opAt 1696 (.Swap ⟨0, by decide⟩),
   pushAt 1697 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1698 .ADD,
   opAt 1699 (.Swap ⟨0, by decide⟩),
   opAt 1700 (.Swap ⟨1, by decide⟩),
   pushAt 1701 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1702 .ADD,
   opAt 1703 (.Swap ⟨1, by decide⟩),
   pushAt 1704 2 8224,
   opAt 1705 (.Dup ⟨1, by decide⟩),
   opAt 1706 .GT,
   pushAt 1707 2 2315,
   opAt 1708 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1709 .POP,
   opAt 1710 .POP,
   opAt 1711 .POP,
   opAt 1712 .ISZERO,
   pushAt 1713 2 8224,
   opAt 1714 .MLOAD,
   opAt 1715 .OR,
   pushAt 1716 2 1087, opAt 1717 .NOT,
   opAt 1718 .MUL,
   pushAt 1719 2 8256,
   opAt 1720 .ADD,
   pushAt 1721 2 9344,
   opAt 1722 .MLOAD,
   opAt 1723 (.Swap ⟨1, by decide⟩),
   opAt 1724 .MCOPY,
   opAt 1725 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
