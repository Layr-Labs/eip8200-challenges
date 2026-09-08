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
  [opAt 1541 .POP,
   opAt 1542 .POP,
   opAt 1543 (.Swap ⟨1, by decide⟩),
   opAt 1544 .POP,
   opAt 1545 .POP,
      opAt 1546 (.Dup ⟨0, by decide⟩),
   pushAt 1547 2 8224,
   opAt 1548 .MLOAD,
   opAt 1549 .ADD,
   opAt 1550 (.Dup ⟨0, by decide⟩),
   pushAt 1551 2 8256,
   opAt 1552 .MSTORE,
   opAt 1553 .LT,
   pushAt 1554 2 8192,
   opAt 1555 .MLOAD,
   opAt 1556 .ADD,
   pushAt 1557 2 8224,
   opAt 1558 .MSTORE,
   pushAt 1559 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1560 .ADD,
   opAt 1561 (.Dup ⟨2, by decide⟩),
   opAt 1562 (.Dup ⟨1, by decide⟩),
   opAt 1563 .GT,
   pushAt 1564 2 1943,
   opAt 1565 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2466. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1566 .POP,
   opAt 1567 .POP,
   opAt 1568 .POP,
   pushAt 1569 2 2497,
   opAt 1570 .JUMP]

/-- Instructions 1600..1626, pc 2467..2499. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1571 .JUMPDEST,
   pushAt 1572 2 9344,
   opAt 1573 .MLOAD,
   opAt 1574 (.Dup ⟨0, by decide⟩),
   opAt 1575 (.Dup ⟨2, by decide⟩),
   opAt 1576 .ADD,
   pushAt 1577 1 32,
   opAt 1578 (.Swap ⟨0, by decide⟩),
   opAt 1579 .SUB,
   opAt 1580 (.Dup ⟨1, by decide⟩),
   opAt 1581 (.Dup ⟨4, by decide⟩),
   opAt 1582 .ADD,
   pushAt 1583 1 32,
   opAt 1584 (.Swap ⟨0, by decide⟩),
   opAt 1585 .SUB,
   opAt 1586 (.Swap ⟨2, by decide⟩),
   opAt 1587 .POP,
   opAt 1588 (.Swap ⟨2, by decide⟩),
   opAt 1589 .POP,
   opAt 1590 .POP,
   pushAt 1591 2 9440,
   opAt 1592 .MLOAD,
   pushAt 1593 0 0,
         opAt 1594 (.Swap ⟨2, by decide⟩),
   opAt 1595 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
