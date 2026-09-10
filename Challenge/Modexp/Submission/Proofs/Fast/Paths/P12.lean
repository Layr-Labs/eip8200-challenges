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
  [opAt 1604 .JUMPDEST,
   opAt 1605 (.Dup ⟨1, by decide⟩),
   opAt 1606 .MLOAD,
   opAt 1607 (.Dup ⟨3, by decide⟩),
   opAt 1608 .MLOAD,
   opAt 1609 (.Dup ⟨1, by decide⟩),
   opAt 1610 .ADD,
   opAt 1611 (.Swap ⟨0, by decide⟩),
   opAt 1612 (.Dup ⟨1, by decide⟩),
   opAt 1613 .LT,
   opAt 1614 (.Swap ⟨0, by decide⟩),
   opAt 1615 (.Dup ⟨5, by decide⟩),
   opAt 1616 .ADD,
   opAt 1617 (.Swap ⟨4, by decide⟩),
   opAt 1618 (.Dup ⟨5, by decide⟩),
   opAt 1619 .LT,
   opAt 1620 .OR,
   opAt 1621 (.Swap ⟨3, by decide⟩),
   opAt 1622 (.Dup ⟨1, by decide⟩),
   opAt 1623 .MSTORE,
   pushAt 1624 1 31,
   opAt 1625 .NOT,
   opAt 1626 .ADD,
   opAt 1627 (.Swap ⟨0, by decide⟩),
   pushAt 1628 1 31,
   opAt 1629 .NOT,
   opAt 1630 .ADD,
   opAt 1631 (.Swap ⟨0, by decide⟩),
   opAt 1632 (.Swap ⟨1, by decide⟩),
   pushAt 1633 1 31,
   opAt 1634 .NOT,
   opAt 1635 .ADD,
   opAt 1636 (.Swap ⟨1, by decide⟩),
   pushAt 1637 2 8224,
   opAt 1638 (.Dup ⟨1, by decide⟩),
   opAt 1639 .GT,
   pushAt 1640 2 2173,
   opAt 1641 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1642 .POP,
   opAt 1643 .POP,
   opAt 1644 .POP,
   pushAt 1645 2 8224,
   opAt 1646 .MSTORE]

/-- Instructions 1667..1682, pc 2309..2332. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1647 .JUMPDEST,
   pushAt 1648 2 9440,
   opAt 1649 .MLOAD,
   pushAt 1650 0 0,
   opAt 1651 (.Swap ⟨0, by decide⟩),
   opAt 1652 (.Dup ⟨0, by decide⟩),
   pushAt 1653 1 32,
   opAt 1654 .AND,
   opAt 1655 .ISZERO,
   pushAt 1656 2 2366,
   opAt 1657 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
