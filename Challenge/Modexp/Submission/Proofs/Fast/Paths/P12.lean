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
  [opAt 1613 .JUMPDEST,
   opAt 1614 (.Dup ⟨1, by decide⟩),
   opAt 1615 .MLOAD,
   opAt 1616 (.Dup ⟨3, by decide⟩),
   opAt 1617 .MLOAD,
   opAt 1618 (.Dup ⟨1, by decide⟩),
   opAt 1619 .ADD,
   opAt 1620 (.Swap ⟨0, by decide⟩),
   opAt 1621 (.Dup ⟨1, by decide⟩),
   opAt 1622 .LT,
   opAt 1623 (.Swap ⟨0, by decide⟩),
   opAt 1624 (.Dup ⟨5, by decide⟩),
   opAt 1625 .ADD,
   opAt 1626 (.Swap ⟨4, by decide⟩),
   opAt 1627 (.Dup ⟨5, by decide⟩),
   opAt 1628 .LT,
   opAt 1629 .OR,
   opAt 1630 (.Swap ⟨3, by decide⟩),
   opAt 1631 (.Dup ⟨1, by decide⟩),
   opAt 1632 .MSTORE,
   pushAt 1633 1 31, opAt 1634 .NOT,
   opAt 1635 .ADD,
   opAt 1636 (.Swap ⟨0, by decide⟩),
   pushAt 1637 1 31, opAt 1638 .NOT,
   opAt 1639 .ADD,
   opAt 1640 (.Swap ⟨0, by decide⟩),
   opAt 1641 (.Swap ⟨1, by decide⟩),
   pushAt 1642 1 31, opAt 1643 .NOT,
   opAt 1644 .ADD,
   opAt 1645 (.Swap ⟨1, by decide⟩),
   pushAt 1646 2 8224,
   opAt 1647 (.Dup ⟨1, by decide⟩),
   opAt 1648 .GT,
   pushAt 1649 2 2240,
   opAt 1650 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1651 .POP,
   opAt 1652 .POP,
   opAt 1653 .POP,
   pushAt 1654 2 8224,
   opAt 1655 .MSTORE]

/-- Instructions 1667..1682, pc 2309..2332. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1656 .JUMPDEST,
   pushAt 1657 2 9440,
   opAt 1658 .MLOAD,
   pushAt 1659 2 9408,
   opAt 1660 .MLOAD,
   opAt 1661 (.Dup ⟨0, by decide⟩),
   pushAt 1662 2 7168,
   opAt 1663 .ADD,
   pushAt 1664 2 8256,
      opAt 1665 .POP,
   pushAt 1666 0 0,
   opAt 1667 (.Swap ⟨2, by decide⟩),
   opAt 1668 (.Swap ⟨0, by decide⟩),
   opAt 1669 (.Swap ⟨1, by decide⟩),
   opAt 1670 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
