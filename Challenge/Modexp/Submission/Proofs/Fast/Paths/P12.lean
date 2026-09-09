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
  [opAt 1621 .JUMPDEST,
   opAt 1622 (.Dup ⟨1, by decide⟩),
   opAt 1623 .MLOAD,
   opAt 1624 (.Dup ⟨3, by decide⟩),
   opAt 1625 .MLOAD,
   opAt 1626 (.Dup ⟨1, by decide⟩),
   opAt 1627 .ADD,
   opAt 1628 (.Swap ⟨0, by decide⟩),
   opAt 1629 (.Dup ⟨1, by decide⟩),
   opAt 1630 .LT,
   opAt 1631 (.Swap ⟨0, by decide⟩),
   opAt 1632 (.Dup ⟨5, by decide⟩),
   opAt 1633 .ADD,
   opAt 1634 (.Swap ⟨4, by decide⟩),
   opAt 1635 (.Dup ⟨5, by decide⟩),
   opAt 1636 .LT,
   opAt 1637 .OR,
   opAt 1638 (.Swap ⟨3, by decide⟩),
   opAt 1639 (.Dup ⟨1, by decide⟩),
   opAt 1640 .MSTORE,
   pushAt 1641 1 31, opAt 1642 .NOT,
   opAt 1643 .ADD,
   opAt 1644 (.Swap ⟨0, by decide⟩),
   pushAt 1645 1 31, opAt 1646 .NOT,
   opAt 1647 .ADD,
   opAt 1648 (.Swap ⟨0, by decide⟩),
   opAt 1649 (.Swap ⟨1, by decide⟩),
   pushAt 1650 1 31, opAt 1651 .NOT,
   opAt 1652 .ADD,
   opAt 1653 (.Swap ⟨1, by decide⟩),
   pushAt 1654 2 8224,
   opAt 1655 (.Dup ⟨1, by decide⟩),
   opAt 1656 .GT,
   pushAt 1657 2 2236,
   opAt 1658 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1659 .POP,
   opAt 1660 .POP,
   opAt 1661 .POP,
   pushAt 1662 2 8224,
   opAt 1663 .MSTORE]

end Challenge.Modexp.Submission.Proofs.Fast
