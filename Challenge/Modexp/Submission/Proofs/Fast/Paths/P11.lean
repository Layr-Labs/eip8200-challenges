import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1626). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1594, pc 2179..2459. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1548 .POP,
   opAt 1549 .POP,
   opAt 1550 (.Swap ⟨1, by decide⟩),
   opAt 1551 .POP,
   opAt 1552 .POP,
   opAt 1553 (.Dup ⟨0, by decide⟩),
   pushAt 1554 2 8224,
   opAt 1555 .MLOAD,
   opAt 1556 .ADD,
   opAt 1557 (.Dup ⟨0, by decide⟩),
   pushAt 1558 2 8256,
   opAt 1559 .MSTORE,
   opAt 1560 .LT,
   pushAt 1561 2 8192,
   opAt 1562 .MLOAD,
   opAt 1563 .ADD,
   pushAt 1564 2 8224,
   opAt 1565 .MSTORE,
   pushAt 1566 1 31,
   opAt 1567 .NOT,
   opAt 1568 .ADD,
   opAt 1569 (.Dup ⟨2, by decide⟩),
   opAt 1570 (.Dup ⟨1, by decide⟩),
   opAt 1571 .GT,
   pushAt 1572 2 1905,
   opAt 1573 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1574 .POP,
   opAt 1575 .POP,
   opAt 1576 .POP,
   pushAt 1577 2 2225,
   opAt 1578 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1579 .JUMPDEST,
   pushAt 1580 2 9344,
   opAt 1581 .MLOAD,
   opAt 1582 (.Dup ⟨0, by decide⟩),
   opAt 1583 (.Dup ⟨2, by decide⟩),
   opAt 1584 .ADD,
   pushAt 1585 1 32,
   opAt 1586 (.Swap ⟨0, by decide⟩),
   opAt 1587 .SUB,
   opAt 1588 (.Dup ⟨1, by decide⟩),
   opAt 1589 (.Dup ⟨4, by decide⟩),
   opAt 1590 .ADD,
   pushAt 1591 1 32,
   opAt 1592 (.Swap ⟨0, by decide⟩),
   opAt 1593 .SUB,
   opAt 1594 (.Swap ⟨2, by decide⟩),
   opAt 1595 .POP,
   opAt 1596 (.Swap ⟨2, by decide⟩),
   opAt 1597 .POP,
   opAt 1598 .POP,
   pushAt 1599 2 9440,
   opAt 1600 .MLOAD,
   pushAt 1601 0 0,
   opAt 1602 (.Swap ⟨2, by decide⟩),
   opAt 1603 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
