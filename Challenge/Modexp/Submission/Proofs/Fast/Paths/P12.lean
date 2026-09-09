import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1627..1682). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1627..1661, pc 2257..2634. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1619 .JUMPDEST,
   opAt 1620 (.Dup ⟨1, by decide⟩),
   opAt 1621 .MLOAD,
   opAt 1622 (.Dup ⟨3, by decide⟩),
   opAt 1623 .MLOAD,
   opAt 1624 (.Dup ⟨1, by decide⟩),
   opAt 1625 .ADD,
   opAt 1626 (.Swap ⟨0, by decide⟩),
   opAt 1627 (.Dup ⟨1, by decide⟩),
   opAt 1628 .LT,
   opAt 1629 (.Swap ⟨0, by decide⟩),
   opAt 1630 (.Dup ⟨5, by decide⟩),
   opAt 1631 .ADD,
   opAt 1632 (.Swap ⟨4, by decide⟩),
   opAt 1633 (.Dup ⟨5, by decide⟩),
   opAt 1634 .LT,
   opAt 1635 .OR,
   opAt 1636 (.Swap ⟨3, by decide⟩),
   opAt 1637 (.Dup ⟨1, by decide⟩),
   opAt 1638 .MSTORE,
   pushAt 1639 1 31, opAt 1640 .NOT,
   opAt 1641 .ADD,
   opAt 1642 (.Swap ⟨0, by decide⟩),
   pushAt 1643 1 31, opAt 1644 .NOT,
   opAt 1645 .ADD,
   opAt 1646 (.Swap ⟨0, by decide⟩),
   opAt 1647 (.Swap ⟨1, by decide⟩),
   pushAt 1648 1 31, opAt 1649 .NOT,
   opAt 1650 .ADD,
   opAt 1651 (.Swap ⟨1, by decide⟩),
   pushAt 1652 2 8224,
   opAt 1653 (.Dup ⟨1, by decide⟩),
   opAt 1654 .GT,
   pushAt 1655 2 2236,
   opAt 1656 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1657 .POP,
   opAt 1658 .POP,
   opAt 1659 .POP,
   pushAt 1660 2 8224,
   opAt 1661 .MSTORE]

/-- Instructions 1667..1682, pc 2309..2332. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1662 .JUMPDEST,
   pushAt 1663 2 9440,
   opAt 1664 .MLOAD,
   pushAt 1665 2 9408,
   opAt 1666 .MLOAD,
   opAt 1667 (.Dup ⟨0, by decide⟩),
   pushAt 1668 2 7168,
   opAt 1669 .ADD,
   pushAt 1670 2 8256,
   opAt 1671 .JUMPDEST,
   opAt 1672 .POP,
   opAt 1673 (.Swap ⟨0, by decide⟩),
   pushAt 1674 0 0,
   opAt 1675 (.Swap ⟨2, by decide⟩),
   opAt 1676 .JUMPDEST,
   opAt 1677 .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast
