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
  [opAt 1552 .POP,
   opAt 1553 .POP,
   opAt 1554 (.Swap ⟨1, by decide⟩),
   opAt 1555 .POP,
   opAt 1556 .POP,
      opAt 1557 (.Dup ⟨0, by decide⟩),
   pushAt 1558 2 8224,
   opAt 1559 .MLOAD,
   opAt 1560 .ADD,
   opAt 1561 (.Dup ⟨0, by decide⟩),
   pushAt 1562 2 8256,
   opAt 1563 .MSTORE,
   opAt 1564 .LT,
   pushAt 1565 2 8192,
   opAt 1566 .MLOAD,
   opAt 1567 .ADD,
   pushAt 1568 2 8224,
   opAt 1569 .MSTORE,
   pushAt 1570 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1571 .ADD,
   opAt 1572 (.Dup ⟨2, by decide⟩),
   opAt 1573 (.Dup ⟨1, by decide⟩),
   opAt 1574 .GT,
   pushAt 1575 2 1950,
   opAt 1576 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2466. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1577 .POP,
   opAt 1578 .POP,
   opAt 1579 .POP,
   pushAt 1580 2 2610,
   opAt 1581 .JUMP]

/-- Instructions 1600..1626, pc 2467..2499. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1582 .JUMPDEST,
   pushAt 1583 2 9344,
   opAt 1584 .MLOAD,
   opAt 1585 (.Dup ⟨0, by decide⟩),
   opAt 1586 (.Dup ⟨2, by decide⟩),
   opAt 1587 .ADD,
   pushAt 1588 1 32,
   opAt 1589 (.Swap ⟨0, by decide⟩),
   opAt 1590 .SUB,
   opAt 1591 (.Dup ⟨1, by decide⟩),
   opAt 1592 (.Dup ⟨4, by decide⟩),
   opAt 1593 .ADD,
   pushAt 1594 1 32,
   opAt 1595 (.Swap ⟨0, by decide⟩),
   opAt 1596 .SUB,
   opAt 1597 (.Swap ⟨2, by decide⟩),
   opAt 1598 .POP,
   opAt 1599 (.Swap ⟨2, by decide⟩),
   opAt 1600 .POP,
   opAt 1601 .POP,
   pushAt 1602 2 9440,
   opAt 1603 .MLOAD,
   pushAt 1604 0 0,
         opAt 1605 (.Swap ⟨2, by decide⟩),
   opAt 1606 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
