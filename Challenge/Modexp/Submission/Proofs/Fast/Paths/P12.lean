import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1627..1682). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1627..1661, pc 2500..2634. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1617 .JUMPDEST,
   opAt 1618 (.Dup ⟨1, by decide⟩),
   opAt 1619 .MLOAD,
   opAt 1620 (.Dup ⟨3, by decide⟩),
   opAt 1621 .MLOAD,
   opAt 1622 (.Dup ⟨1, by decide⟩),
   opAt 1623 .ADD,
   opAt 1624 (.Swap ⟨0, by decide⟩),
   opAt 1625 (.Dup ⟨1, by decide⟩),
   opAt 1626 .LT,
   opAt 1627 (.Swap ⟨0, by decide⟩),
   opAt 1628 (.Dup ⟨5, by decide⟩),
   opAt 1629 .ADD,
   opAt 1630 (.Swap ⟨4, by decide⟩),
   opAt 1631 (.Dup ⟨5, by decide⟩),
   opAt 1632 .LT,
   opAt 1633 .OR,
   opAt 1634 (.Swap ⟨3, by decide⟩),
   opAt 1635 (.Dup ⟨1, by decide⟩),
   opAt 1636 .MSTORE,
   pushAt 1637 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1638 .ADD,
   opAt 1639 (.Swap ⟨0, by decide⟩),
   pushAt 1640 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1641 .ADD,
   opAt 1642 (.Swap ⟨0, by decide⟩),
   opAt 1643 (.Swap ⟨1, by decide⟩),
   pushAt 1644 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1645 .ADD,
   opAt 1646 (.Swap ⟨1, by decide⟩),
   pushAt 1647 2 8224,
   opAt 1648 (.Dup ⟨1, by decide⟩),
   opAt 1649 .GT,
   pushAt 1650 2 2495,
   opAt 1651 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2641. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1652 .POP,
   opAt 1653 .POP,
   opAt 1654 .POP,
   pushAt 1655 2 8224,
   opAt 1656 .MSTORE]

/-- Instructions 1667..1682, pc 2642..2665. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1657 .JUMPDEST,
   pushAt 1658 2 9440,
   opAt 1659 .MLOAD,
   pushAt 1660 2 9408,
   opAt 1661 .MLOAD,
   opAt 1662 (.Dup ⟨0, by decide⟩),
   pushAt 1663 2 7168,
   opAt 1664 .ADD,
   pushAt 1665 3 8256,
   opAt 1666 .POP,
   pushAt 1667 0 0,
   opAt 1668 (.Swap ⟨2, by decide⟩),
   opAt 1669 (.Swap ⟨0, by decide⟩),
   opAt 1670 (.Swap ⟨1, by decide⟩),
   opAt 1671 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
