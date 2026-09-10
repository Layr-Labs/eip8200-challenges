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
   pushAt 1637 1 31, opAt 1638 .NOT,
   opAt 1639 .ADD,
   opAt 1640 (.Swap ⟨0, by decide⟩),
   pushAt 1641 1 31, opAt 1642 .NOT,
   opAt 1643 .ADD,
   opAt 1644 (.Swap ⟨0, by decide⟩),
   opAt 1645 (.Swap ⟨1, by decide⟩),
   pushAt 1646 1 31, opAt 1647 .NOT,
   opAt 1648 .ADD,
   opAt 1649 (.Swap ⟨1, by decide⟩),
   pushAt 1650 2 8224,
   opAt 1651 (.Dup ⟨1, by decide⟩),
   opAt 1652 .GT,
   pushAt 1653 2 2252,
   opAt 1654 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1655 .POP,
   opAt 1656 .POP,
   opAt 1657 .POP,
   pushAt 1658 2 8224,
   opAt 1659 .MSTORE]

/-- Instructions 1667..1682, pc 2309..2332. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1660 .JUMPDEST,
   pushAt 1661 2 9440,
   opAt 1662 .MLOAD,
   pushAt 1663 2 9408,
   opAt 1664 .MLOAD,
   opAt 1665 (.Dup ⟨0, by decide⟩),
   pushAt 1666 2 7168,
   opAt 1667 .ADD,
   pushAt 1668 2 8256,
   opAt 1669 .JUMPDEST,
   opAt 1670 .POP,
   pushAt 1671 0 0,
   opAt 1672 (.Swap ⟨2, by decide⟩),
   opAt 1673 (.Swap ⟨0, by decide⟩),
   opAt 1674 (.Swap ⟨1, by decide⟩),
   opAt 1675 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
