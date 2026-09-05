import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1626). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1594, pc 2392..2459. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1570 .POP,
   opAt 1571 .POP,
   opAt 1572 (.Swap ⟨0, by decide⟩),
   opAt 1573 .POP,
   opAt 1574 (.Swap ⟨0, by decide⟩),
   opAt 1575 .POP,
   opAt 1576 (.Dup ⟨0, by decide⟩),
   pushAt 1577 2 8224,
   opAt 1578 .MLOAD,
   opAt 1579 .ADD,
   opAt 1580 (.Dup ⟨0, by decide⟩),
   pushAt 1581 2 8256,
   opAt 1582 .MSTORE,
   opAt 1583 .LT,
   pushAt 1584 2 8192,
   opAt 1585 .MLOAD,
   opAt 1586 .ADD,
   pushAt 1587 2 8224,
   opAt 1588 .MSTORE,
   pushAt 1589 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1590 .ADD,
   opAt 1591 (.Dup ⟨2, by decide⟩),
   opAt 1592 (.Dup ⟨1, by decide⟩),
   opAt 1593 .GT,
   pushAt 1594 2 1974,
   opAt 1595 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2466. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1596 .POP,
   opAt 1597 .POP,
   opAt 1598 .POP,
   pushAt 1599 2 2642,
   opAt 1600 .JUMP]

/-- Instructions 1600..1626, pc 2467..2499. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1601 .JUMPDEST,
   pushAt 1602 2 9344,
   opAt 1603 .MLOAD,
   opAt 1604 (.Dup ⟨0, by decide⟩),
   opAt 1605 (.Dup ⟨2, by decide⟩),
   opAt 1606 .ADD,
   pushAt 1607 1 32,
   opAt 1608 (.Swap ⟨0, by decide⟩),
   opAt 1609 .SUB,
   opAt 1610 (.Dup ⟨1, by decide⟩),
   opAt 1611 (.Dup ⟨4, by decide⟩),
   opAt 1612 .ADD,
   pushAt 1613 1 32,
   opAt 1614 (.Swap ⟨0, by decide⟩),
   opAt 1615 .SUB,
   opAt 1616 (.Swap ⟨2, by decide⟩),
   opAt 1617 .POP,
   opAt 1618 (.Swap ⟨2, by decide⟩),
   opAt 1619 .POP,
   opAt 1620 .POP,
   pushAt 1621 2 9440,
   opAt 1622 .MLOAD,
   pushAt 1623 0 0,
   opAt 1624 (.Swap ⟨0, by decide⟩),
   opAt 1625 (.Swap ⟨0, by decide⟩),
   opAt 1626 (.Swap ⟨2, by decide⟩),
   opAt 1627 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
