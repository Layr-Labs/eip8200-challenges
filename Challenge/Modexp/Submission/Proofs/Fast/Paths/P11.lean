import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1590..1651). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The row-tail block, instructions 1590..1616, pc 2417..2485. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1590 .JUMPDEST,
   opAt 1591 .POP,
   opAt 1592 .POP,
   opAt 1593 (.Swap ⟨0, by decide⟩),
   opAt 1594 .POP,
   opAt 1595 (.Swap ⟨0, by decide⟩),
   opAt 1596 .POP,
   opAt 1597 (.Dup ⟨0, by decide⟩),
   pushAt 1598 2 8224,
   opAt 1599 .MLOAD,
   opAt 1600 .ADD,
   opAt 1601 (.Dup ⟨0, by decide⟩),
   pushAt 1602 2 8256,
   opAt 1603 .MSTORE,
   opAt 1604 .LT,
   pushAt 1605 2 8192,
   opAt 1606 .MLOAD,
   opAt 1607 .ADD,
   pushAt 1608 2 8224,
   opAt 1609 .MSTORE,
   pushAt 1610 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1611 .ADD,
   opAt 1612 (.Dup ⟨2, by decide⟩),
   opAt 1613 (.Dup ⟨1, by decide⟩),
   opAt 1614 .GT,
   pushAt 1615 2 1982,
   opAt 1616 .JUMPI]

/-- The final row cleanup, instructions 1617..1624, pc 2486..2495. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1617 .POP,
   opAt 1618 .POP,
   opAt 1619 .POP,
   opAt 1620 (.Swap ⟨1, by decide⟩),
   opAt 1621 .POP,
   opAt 1622 (.Swap ⟨0, by decide⟩),
   pushAt 1623 2 2671,
   opAt 1624 .JUMP]

/-- The CSUB continuation, instructions 1625..1651, pc 2496..2528. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1625 .JUMPDEST,
   pushAt 1626 2 9344,
   opAt 1627 .MLOAD,
   opAt 1628 (.Dup ⟨0, by decide⟩),
   opAt 1629 (.Dup ⟨2, by decide⟩),
   opAt 1630 .ADD,
   pushAt 1631 1 32,
   opAt 1632 (.Swap ⟨0, by decide⟩),
   opAt 1633 .SUB,
   opAt 1634 (.Dup ⟨1, by decide⟩),
   opAt 1635 (.Dup ⟨4, by decide⟩),
   opAt 1636 .ADD,
   pushAt 1637 1 32,
   opAt 1638 (.Swap ⟨0, by decide⟩),
   opAt 1639 .SUB,
   opAt 1640 (.Swap ⟨2, by decide⟩),
   opAt 1641 .POP,
   opAt 1642 (.Swap ⟨2, by decide⟩),
   opAt 1643 .POP,
   opAt 1644 .POP,
   pushAt 1645 2 9440,
   opAt 1646 .MLOAD,
   pushAt 1647 0 0,
   opAt 1648 .JUMPDEST,
   opAt 1649 .JUMPDEST,
   opAt 1650 (.Swap ⟨2, by decide⟩),
   opAt 1651 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
