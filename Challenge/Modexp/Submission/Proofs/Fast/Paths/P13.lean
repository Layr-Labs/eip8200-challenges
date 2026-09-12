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
  [opAt 1553 .JUMPDEST,
   opAt 1554 (.Dup ⟨0, by decide⟩),
   opAt 1555 .MLOAD,
   opAt 1556 (.Dup ⟨2, by decide⟩),
   opAt 1557 .MLOAD,
   opAt 1558 (.Dup ⟨1, by decide⟩),
   opAt 1559 (.Dup ⟨1, by decide⟩),
   opAt 1560 .GT,
   opAt 1561 (.Swap ⟨1, by decide⟩),
   opAt 1562 .SUB,
   opAt 1563 (.Dup ⟨5, by decide⟩),
   opAt 1564 (.Dup ⟨1, by decide⟩),
   opAt 1565 .SUB,
   opAt 1566 (.Swap ⟨0, by decide⟩),
   opAt 1567 (.Dup ⟨6, by decide⟩),
   opAt 1568 .GT,
   opAt 1569 (.Swap ⟨0, by decide⟩),
   opAt 1570 (.Swap ⟨1, by decide⟩),
   opAt 1571 .OR,
   opAt 1572 (.Swap ⟨4, by decide⟩),
   opAt 1573 .POP,
   opAt 1574 (.Dup ⟨3, by decide⟩),
   opAt 1575 .MSTORE,
   pushAt 1576 1 31,
   opAt 1577 .NOT,
   opAt 1578 .ADD,
   opAt 1579 (.Swap ⟨0, by decide⟩),
   pushAt 1580 1 31,
   opAt 1581 .NOT,
   opAt 1582 .ADD,
   opAt 1583 (.Swap ⟨0, by decide⟩),
   opAt 1584 (.Swap ⟨1, by decide⟩),
   pushAt 1585 1 31,
   opAt 1586 .NOT,
   opAt 1587 .ADD,
   opAt 1588 (.Swap ⟨1, by decide⟩),
   pushAt 1589 2 4128,
   opAt 1590 (.Dup ⟨1, by decide⟩),
   opAt 1591 .GT,
   pushAt 1592 2 2120,
   opAt 1593 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1594 .POP,
   opAt 1595 .POP,
   opAt 1596 .POP,
   opAt 1597 .ISZERO,
   pushAt 1598 2 4128,
   opAt 1599 .MLOAD,
   opAt 1600 .OR,
   pushAt 1601 2 1087,
   opAt 1602 .NOT,
   opAt 1603 .MUL,
   pushAt 1604 2 4160,
   opAt 1605 .ADD,
   pushAt 1606 2 5248,
   opAt 1607 .MLOAD,
   opAt 1608 (.Swap ⟨1, by decide⟩),
   opAt 1609 .MCOPY,
   opAt 1610 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
