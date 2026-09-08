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
  [opAt 1618 .JUMPDEST,
   opAt 1619 (.Dup ⟨1, by decide⟩),
   opAt 1620 .MLOAD,
   opAt 1621 (.Dup ⟨3, by decide⟩),
   opAt 1622 .MLOAD,
   opAt 1623 (.Dup ⟨1, by decide⟩),
   opAt 1624 .ADD,
   opAt 1625 (.Swap ⟨0, by decide⟩),
   opAt 1626 (.Dup ⟨1, by decide⟩),
   opAt 1627 .LT,
   opAt 1628 (.Swap ⟨0, by decide⟩),
   opAt 1629 (.Dup ⟨5, by decide⟩),
   opAt 1630 .ADD,
   opAt 1631 (.Swap ⟨4, by decide⟩),
   opAt 1632 (.Dup ⟨5, by decide⟩),
   opAt 1633 .LT,
   opAt 1634 .OR,
   opAt 1635 (.Swap ⟨3, by decide⟩),
   opAt 1636 (.Dup ⟨1, by decide⟩),
   opAt 1637 .MSTORE,
   pushAt 1638 1 31, opAt 1639 .NOT,
   opAt 1640 .ADD,
   opAt 1641 (.Swap ⟨0, by decide⟩),
   pushAt 1642 1 31, opAt 1643 .NOT,
   opAt 1644 .ADD,
   opAt 1645 (.Swap ⟨0, by decide⟩),
   opAt 1646 (.Swap ⟨1, by decide⟩),
   pushAt 1647 1 31, opAt 1648 .NOT,
   opAt 1649 .ADD,
   opAt 1650 (.Swap ⟨1, by decide⟩),
   pushAt 1651 2 8224,
   opAt 1652 (.Dup ⟨1, by decide⟩),
   opAt 1653 .GT,
   pushAt 1654 2 2465,
   opAt 1655 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2641. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1656 .POP,
   opAt 1657 .POP,
   opAt 1658 .POP,
   pushAt 1659 2 8224,
   opAt 1660 .MSTORE]

/-- Instructions 1667..1682, pc 2642..2665. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1661 .JUMPDEST,
   pushAt 1662 2 9440,
   opAt 1663 .MLOAD,
   pushAt 1664 2 9408,
   opAt 1665 .MLOAD,
   opAt 1666 (.Dup ⟨0, by decide⟩),
   pushAt 1667 2 7168,
   opAt 1668 .ADD,
   pushAt 1669 2 8256,
   opAt 1670 .JUMPDEST,
   opAt 1671 .POP,
   pushAt 1672 0 0,
   opAt 1673 (.Swap ⟨2, by decide⟩),
   opAt 1674 (.Swap ⟨0, by decide⟩),
   opAt 1675 (.Swap ⟨1, by decide⟩),
   opAt 1676 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
