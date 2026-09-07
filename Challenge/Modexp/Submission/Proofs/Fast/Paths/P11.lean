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
  [opAt 1564 .POP,
   opAt 1565 .POP,
   opAt 1566 (.Swap ⟨1, by decide⟩),
   opAt 1567 .POP,
   opAt 1568 .POP,
   opAt 1569 .JUMPDEST,
   opAt 1570 (.Dup ⟨0, by decide⟩),
   pushAt 1571 2 8224,
   opAt 1572 .MLOAD,
   opAt 1573 .ADD,
   opAt 1574 (.Dup ⟨0, by decide⟩),
   pushAt 1575 2 8256,
   opAt 1576 .MSTORE,
   opAt 1577 .LT,
   pushAt 1578 2 8192,
   opAt 1579 .MLOAD,
   opAt 1580 .ADD,
   pushAt 1581 2 8224,
   opAt 1582 .MSTORE,
   pushAt 1583 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1584 .ADD,
   opAt 1585 (.Dup ⟨2, by decide⟩),
   opAt 1586 (.Dup ⟨1, by decide⟩),
   opAt 1587 .GT,
   pushAt 1588 2 1974,
   opAt 1589 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2466. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1590 .POP,
   opAt 1591 .POP,
   opAt 1592 .POP,
   pushAt 1593 2 2642,
   opAt 1594 .JUMP]

/-- Instructions 1600..1626, pc 2467..2499. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1595 .JUMPDEST,
   pushAt 1596 2 9344,
   opAt 1597 .MLOAD,
   opAt 1598 (.Dup ⟨0, by decide⟩),
   opAt 1599 (.Dup ⟨2, by decide⟩),
   opAt 1600 .ADD,
   pushAt 1601 1 32,
   opAt 1602 (.Swap ⟨0, by decide⟩),
   opAt 1603 .SUB,
   opAt 1604 (.Dup ⟨1, by decide⟩),
   opAt 1605 (.Dup ⟨4, by decide⟩),
   opAt 1606 .ADD,
   pushAt 1607 1 32,
   opAt 1608 (.Swap ⟨0, by decide⟩),
   opAt 1609 .SUB,
   opAt 1610 (.Swap ⟨2, by decide⟩),
   opAt 1611 .POP,
   opAt 1612 (.Swap ⟨2, by decide⟩),
   opAt 1613 .POP,
   opAt 1614 .POP,
   pushAt 1615 2 9440,
   opAt 1616 .MLOAD,
   pushAt 1617 0 0,
   opAt 1618 .JUMPDEST,
   opAt 1619 .JUMPDEST,
   opAt 1620 (.Swap ⟨2, by decide⟩),
   opAt 1621 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
