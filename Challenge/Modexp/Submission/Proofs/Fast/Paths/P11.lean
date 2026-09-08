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
  [opAt 1557 .POP,
   opAt 1558 .POP,
   opAt 1559 (.Swap ⟨1, by decide⟩),
   opAt 1560 .POP,
   opAt 1561 .POP,
      opAt 1562 (.Dup ⟨0, by decide⟩),
   pushAt 1563 2 8224,
   opAt 1564 .MLOAD,
   opAt 1565 .ADD,
   opAt 1566 (.Dup ⟨0, by decide⟩),
   pushAt 1567 2 8256,
   opAt 1568 .MSTORE,
   opAt 1569 .LT,
   pushAt 1570 2 8192,
   opAt 1571 .MLOAD,
   opAt 1572 .ADD,
   pushAt 1573 2 8224,
   opAt 1574 .MSTORE,
   pushAt 1575 1 31, opAt 1576 .NOT,
   opAt 1577 .ADD,
   opAt 1578 (.Dup ⟨2, by decide⟩),
   opAt 1579 (.Dup ⟨1, by decide⟩),
   opAt 1580 .GT,
   pushAt 1581 2 1965,
   opAt 1582 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1583 .POP,
   opAt 1584 .POP,
   opAt 1585 .POP,
   pushAt 1586 2 2292,
   opAt 1587 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1588 .JUMPDEST,
   pushAt 1589 2 9344,
   opAt 1590 .MLOAD,
   opAt 1591 (.Dup ⟨0, by decide⟩),
   opAt 1592 (.Dup ⟨2, by decide⟩),
   opAt 1593 .ADD,
   pushAt 1594 1 32,
   opAt 1595 (.Swap ⟨0, by decide⟩),
   opAt 1596 .SUB,
   opAt 1597 (.Dup ⟨1, by decide⟩),
   opAt 1598 (.Dup ⟨4, by decide⟩),
   opAt 1599 .ADD,
   pushAt 1600 1 32,
   opAt 1601 (.Swap ⟨0, by decide⟩),
   opAt 1602 .SUB,
   opAt 1603 (.Swap ⟨2, by decide⟩),
   opAt 1604 .POP,
   opAt 1605 (.Swap ⟨2, by decide⟩),
   opAt 1606 .POP,
   opAt 1607 .POP,
   pushAt 1608 2 9440,
   opAt 1609 .MLOAD,
   pushAt 1610 0 0,
         opAt 1611 (.Swap ⟨2, by decide⟩),
   opAt 1612 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
