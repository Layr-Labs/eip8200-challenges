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
  [opAt 1559 .POP,
   opAt 1560 .POP,
   opAt 1561 (.Swap ⟨1, by decide⟩),
   opAt 1562 .POP,
   opAt 1563 .POP,
   opAt 1564 .JUMPDEST,
   opAt 1565 (.Dup ⟨0, by decide⟩),
   pushAt 1566 2 8224,
   opAt 1567 .MLOAD,
   opAt 1568 .ADD,
   opAt 1569 (.Dup ⟨0, by decide⟩),
   pushAt 1570 2 8256,
   opAt 1571 .MSTORE,
   opAt 1572 .LT,
   pushAt 1573 2 8192,
   opAt 1574 .MLOAD,
   opAt 1575 .ADD,
   pushAt 1576 2 8224,
   opAt 1577 .MSTORE,
   pushAt 1578 1 31, opAt 1579 .NOT,
   opAt 1580 .ADD,
   opAt 1581 (.Dup ⟨2, by decide⟩),
   opAt 1582 (.Dup ⟨1, by decide⟩),
   opAt 1583 .GT,
   pushAt 1584 2 1974,
   opAt 1585 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2466. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1586 .POP,
   opAt 1587 .POP,
   opAt 1588 .POP,
   pushAt 1589 2 2517,
   opAt 1590 .JUMP]

/-- Instructions 1600..1626, pc 2467..2499. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1591 .JUMPDEST,
   pushAt 1592 2 9344,
   opAt 1593 .MLOAD,
   opAt 1594 (.Dup ⟨0, by decide⟩),
   opAt 1595 (.Dup ⟨2, by decide⟩),
   opAt 1596 .ADD,
   pushAt 1597 1 32,
   opAt 1598 (.Swap ⟨0, by decide⟩),
   opAt 1599 .SUB,
   opAt 1600 (.Dup ⟨1, by decide⟩),
   opAt 1601 (.Dup ⟨4, by decide⟩),
   opAt 1602 .ADD,
   pushAt 1603 1 32,
   opAt 1604 (.Swap ⟨0, by decide⟩),
   opAt 1605 .SUB,
   opAt 1606 (.Swap ⟨2, by decide⟩),
   opAt 1607 .POP,
   opAt 1608 (.Swap ⟨2, by decide⟩),
   opAt 1609 .POP,
   opAt 1610 .POP,
   pushAt 1611 2 9440,
   opAt 1612 .MLOAD,
   pushAt 1613 0 0,
   opAt 1614 .JUMPDEST,
   opAt 1615 .JUMPDEST,
   opAt 1616 (.Swap ⟨2, by decide⟩),
   opAt 1617 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
