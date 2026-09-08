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
  [opAt 1596 .JUMPDEST,
   opAt 1597 (.Dup ⟨1, by decide⟩),
   opAt 1598 .MLOAD,
   opAt 1599 (.Dup ⟨3, by decide⟩),
   opAt 1600 .MLOAD,
   opAt 1601 (.Dup ⟨1, by decide⟩),
   opAt 1602 .ADD,
   opAt 1603 (.Swap ⟨0, by decide⟩),
   opAt 1604 (.Dup ⟨1, by decide⟩),
   opAt 1605 .LT,
   opAt 1606 (.Swap ⟨0, by decide⟩),
   opAt 1607 (.Dup ⟨5, by decide⟩),
   opAt 1608 .ADD,
   opAt 1609 (.Swap ⟨4, by decide⟩),
   opAt 1610 (.Dup ⟨5, by decide⟩),
   opAt 1611 .LT,
   opAt 1612 .OR,
   opAt 1613 (.Swap ⟨3, by decide⟩),
   opAt 1614 (.Dup ⟨1, by decide⟩),
   opAt 1615 .MSTORE,
   pushAt 1616 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1617 .ADD,
   opAt 1618 (.Swap ⟨0, by decide⟩),
   pushAt 1619 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1620 .ADD,
   opAt 1621 (.Swap ⟨0, by decide⟩),
   opAt 1622 (.Swap ⟨1, by decide⟩),
   pushAt 1623 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1624 .ADD,
   opAt 1625 (.Swap ⟨1, by decide⟩),
   pushAt 1626 2 8224,
   opAt 1627 (.Dup ⟨1, by decide⟩),
   opAt 1628 .GT,
   pushAt 1629 2 2355,
   opAt 1630 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2641. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1631 .POP,
   opAt 1632 .POP,
   opAt 1633 .POP,
   pushAt 1634 2 8224,
   opAt 1635 .MSTORE]

/-- Instructions 1667..1682, pc 2642..2665. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1636 .JUMPDEST,
   pushAt 1637 2 9440,
   opAt 1638 .MLOAD,
   pushAt 1639 2 9408,
   opAt 1640 .MLOAD,
   opAt 1641 (.Dup ⟨0, by decide⟩),
   pushAt 1642 2 7168,
   opAt 1643 .ADD,
   pushAt 1644 2 8256,
      opAt 1645 .POP,
   pushAt 1646 0 0,
   opAt 1647 (.Swap ⟨2, by decide⟩),
   opAt 1648 (.Swap ⟨0, by decide⟩),
   opAt 1649 (.Swap ⟨1, by decide⟩),
   opAt 1650 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
