import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1683..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- New one-pointer `CSUB` loop body: instructions 1673..1706, pc 2337..2470. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1673 .JUMPDEST,
   opAt 1674 (.Dup ⟨0, by decide⟩),
   opAt 1675 .MLOAD,
   pushAt 1676 32 115792089237316195423570985008687907853269984665640564039457584007913129631680,
   opAt 1677 (.Dup ⟨2, by decide⟩),
   opAt 1678 .ADD,
   opAt 1679 .MLOAD,
   opAt 1680 (.Dup ⟨1, by decide⟩),
   opAt 1681 (.Dup ⟨1, by decide⟩),
   opAt 1682 .GT,
   opAt 1683 (.Swap ⟨1, by decide⟩),
   opAt 1684 .SUB,
   opAt 1685 (.Dup ⟨3, by decide⟩),
   opAt 1686 (.Dup ⟨1, by decide⟩),
   opAt 1687 .SUB,
   opAt 1688 (.Swap ⟨0, by decide⟩),
   opAt 1689 (.Dup ⟨4, by decide⟩),
   opAt 1690 .GT,
   opAt 1691 (.Swap ⟨0, by decide⟩),
   opAt 1692 (.Swap ⟨1, by decide⟩),
   opAt 1693 .OR,
   opAt 1694 (.Swap ⟨2, by decide⟩),
   opAt 1695 .POP,
   pushAt 1696 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1697 (.Dup ⟨2, by decide⟩),
   opAt 1698 .ADD,
   opAt 1699 .MSTORE,
   pushAt 1700 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1701 .ADD,
   pushAt 1702 2 8224,
   opAt 1703 (.Dup ⟨1, by decide⟩),
   opAt 1704 .GT,
   pushAt 1705 2 2337,
   opAt 1706 .JUMPI]

/-- Stale-pointer `POP` (pc 2471) plus the common return tail: instructions
1707..1721, pc 2471..2493. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1707 .POP,
   opAt 1708 .ISZERO,
   pushAt 1709 2 8224,
   opAt 1710 .MLOAD,
   opAt 1711 .OR,
   pushAt 1712 2 1087, opAt 1713 .NOT,
   opAt 1714 .MUL,
   pushAt 1715 2 8256,
   opAt 1716 .ADD,
   pushAt 1717 2 9344,
   opAt 1718 .MLOAD,
   opAt 1719 (.Swap ⟨1, by decide⟩),
   opAt 1720 .MCOPY,
   opAt 1721 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
