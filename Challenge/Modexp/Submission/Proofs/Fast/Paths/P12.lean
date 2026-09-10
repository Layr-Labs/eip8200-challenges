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
  [opAt 1625 .JUMPDEST,
   opAt 1626 (.Dup ⟨1, by decide⟩),
   opAt 1627 .MLOAD,
   opAt 1628 (.Dup ⟨3, by decide⟩),
   opAt 1629 .MLOAD,
   opAt 1630 (.Dup ⟨1, by decide⟩),
   opAt 1631 .ADD,
   opAt 1632 (.Swap ⟨0, by decide⟩),
   opAt 1633 (.Dup ⟨1, by decide⟩),
   opAt 1634 .LT,
   opAt 1635 (.Swap ⟨0, by decide⟩),
   opAt 1636 (.Dup ⟨5, by decide⟩),
   opAt 1637 .ADD,
   opAt 1638 (.Swap ⟨4, by decide⟩),
   opAt 1639 (.Dup ⟨5, by decide⟩),
   opAt 1640 .LT,
   opAt 1641 .OR,
   opAt 1642 (.Swap ⟨3, by decide⟩),
   opAt 1643 (.Dup ⟨1, by decide⟩),
   opAt 1644 .MSTORE,
   pushAt 1645 1 31, opAt 1646 .NOT,
   opAt 1647 .ADD,
   opAt 1648 (.Swap ⟨0, by decide⟩),
   pushAt 1649 1 31, opAt 1650 .NOT,
   opAt 1651 .ADD,
   opAt 1652 (.Swap ⟨0, by decide⟩),
   opAt 1653 (.Swap ⟨1, by decide⟩),
   pushAt 1654 1 31, opAt 1655 .NOT,
   opAt 1656 .ADD,
   opAt 1657 (.Swap ⟨1, by decide⟩),
   pushAt 1658 2 8224,
   opAt 1659 (.Dup ⟨1, by decide⟩),
   opAt 1660 .GT,
   pushAt 1661 2 2252,
   opAt 1662 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1663 .POP,
   opAt 1664 .POP,
   opAt 1665 .POP,
   pushAt 1666 2 8224,
   opAt 1667 .MSTORE]

/-- Instructions 1668..1672, pc 2304..2336: new one-pointer `CSUB` entry.
Reads word 9440 for the `t` top pointer and pushes borrow `0`. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1668 .JUMPDEST,
   pushAt 1669 28 9440,
   opAt 1670 .MLOAD,
   pushAt 1671 0 0,
   opAt 1672 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
