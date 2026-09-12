import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1813..1823). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1813..1853, pc 2414..2611. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1550 .JUMPDEST,
   opAt 1551 (.Dup ⟨0, by decide⟩),
   opAt 1552 .MLOAD,
   opAt 1553 (.Dup ⟨2, by decide⟩),
   opAt 1554 .MLOAD,
   opAt 1555 (.Dup ⟨1, by decide⟩),
   opAt 1556 (.Dup ⟨1, by decide⟩),
   opAt 1557 .GT,
   opAt 1558 (.Swap ⟨1, by decide⟩),
   opAt 1559 .SUB,
   opAt 1560 (.Dup ⟨5, by decide⟩),
   opAt 1561 (.Dup ⟨1, by decide⟩),
   opAt 1562 .SUB,
   opAt 1563 (.Swap ⟨0, by decide⟩),
   opAt 1564 (.Dup ⟨6, by decide⟩),
   opAt 1565 .GT,
   opAt 1566 (.Swap ⟨0, by decide⟩),
   opAt 1567 (.Swap ⟨1, by decide⟩),
   opAt 1568 .OR,
   opAt 1569 (.Swap ⟨4, by decide⟩),
   opAt 1570 .POP,
   opAt 1571 (.Dup ⟨3, by decide⟩),
   opAt 1572 .MSTORE,
   pushAt 1573 1 31,
   opAt 1574 .NOT,
   opAt 1575 .ADD,
   opAt 1576 (.Swap ⟨0, by decide⟩),
   pushAt 1577 1 31,
   opAt 1578 .NOT,
   opAt 1579 .ADD,
   opAt 1580 (.Swap ⟨0, by decide⟩),
   opAt 1581 (.Swap ⟨1, by decide⟩),
   pushAt 1582 1 31,
   opAt 1583 .NOT,
   opAt 1584 .ADD,
   opAt 1585 (.Swap ⟨1, by decide⟩),
   pushAt 1586 2 4128,
   opAt 1587 (.Dup ⟨1, by decide⟩),
   opAt 1588 .GT,
   pushAt 1589 2 2115,
   opAt 1590 .JUMPI]

/-- Live instructions 1854..1869, pc 2848..2998; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1591 .POP,
   opAt 1592 .POP,
   opAt 1593 .POP,
   opAt 1594 .ISZERO,
   pushAt 1595 2 4128,
   opAt 1596 .MLOAD,
   opAt 1597 .OR,
   pushAt 1598 2 1087,
   opAt 1599 .NOT,
   opAt 1600 .MUL,
   pushAt 1601 2 4160,
   opAt 1602 .ADD,
   pushAt 1603 2 5248,
   opAt 1604 .MLOAD,
   opAt 1605 (.Swap ⟨1, by decide⟩),
   opAt 1606 .MCOPY,
   opAt 1607 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
