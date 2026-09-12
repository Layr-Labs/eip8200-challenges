import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1683..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1683..1723, pc 2333..2473. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1552 .JUMPDEST,
   opAt 1553 (.Dup ⟨0, by decide⟩),
   opAt 1554 .MLOAD,
   opAt 1555 (.Dup ⟨2, by decide⟩),
   opAt 1556 .MLOAD,
   opAt 1557 (.Dup ⟨1, by decide⟩),
   opAt 1558 (.Dup ⟨1, by decide⟩),
   opAt 1559 .GT,
   opAt 1560 (.Swap ⟨1, by decide⟩),
   opAt 1561 .SUB,
   opAt 1562 (.Dup ⟨5, by decide⟩),
   opAt 1563 (.Dup ⟨1, by decide⟩),
   opAt 1564 .SUB,
   opAt 1565 (.Swap ⟨0, by decide⟩),
   opAt 1566 (.Dup ⟨6, by decide⟩),
   opAt 1567 .GT,
   opAt 1568 (.Swap ⟨0, by decide⟩),
   opAt 1569 (.Swap ⟨1, by decide⟩),
   opAt 1570 .OR,
   opAt 1571 (.Swap ⟨4, by decide⟩),
   opAt 1572 .POP,
   opAt 1573 (.Dup ⟨3, by decide⟩),
   opAt 1574 .MSTORE,
   pushAt 1575 1 31,
   opAt 1576 .NOT,
   opAt 1577 .ADD,
   opAt 1578 (.Swap ⟨0, by decide⟩),
   pushAt 1579 1 31,
   opAt 1580 .NOT,
   opAt 1581 .ADD,
   opAt 1582 (.Swap ⟨0, by decide⟩),
   opAt 1583 (.Swap ⟨1, by decide⟩),
   pushAt 1584 1 31,
   opAt 1585 .NOT,
   opAt 1586 .ADD,
   opAt 1587 (.Swap ⟨1, by decide⟩),
   pushAt 1588 2 8224,
   opAt 1589 (.Dup ⟨1, by decide⟩),
   opAt 1590 .GT,
   pushAt 1591 2 2120,
   opAt 1592 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1593 .POP,
   opAt 1594 .POP,
   opAt 1595 .POP,
   opAt 1596 .ISZERO,
   pushAt 1597 2 8224,
   opAt 1598 .MLOAD,
   opAt 1599 .OR,
   pushAt 1600 2 1087,
   opAt 1601 .NOT,
   opAt 1602 .MUL,
   pushAt 1603 2 8256,
   opAt 1604 .ADD,
   pushAt 1605 2 9344,
   opAt 1606 .MLOAD,
   opAt 1607 (.Swap ⟨1, by decide⟩),
   opAt 1608 .MCOPY,
   opAt 1609 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
