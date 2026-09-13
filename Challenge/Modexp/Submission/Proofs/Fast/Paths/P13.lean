import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1810..1820). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1810..1850, pc 2402..2608. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1549 .JUMPDEST,
   opAt 1550 (.Dup ⟨0, by decide⟩),
   opAt 1551 .MLOAD,
   opAt 1552 (.Dup ⟨2, by decide⟩),
   opAt 1553 .MLOAD,
   opAt 1554 (.Dup ⟨1, by decide⟩),
   opAt 1555 (.Dup ⟨1, by decide⟩),
   opAt 1556 .GT,
   opAt 1557 (.Swap ⟨1, by decide⟩),
   opAt 1558 .SUB,
   opAt 1559 (.Dup ⟨5, by decide⟩),
   opAt 1560 (.Dup ⟨1, by decide⟩),
   opAt 1561 .SUB,
   opAt 1562 (.Swap ⟨0, by decide⟩),
   opAt 1563 (.Dup ⟨6, by decide⟩),
   opAt 1564 .GT,
   opAt 1565 (.Swap ⟨0, by decide⟩),
   opAt 1566 (.Swap ⟨1, by decide⟩),
   opAt 1567 .OR,
   opAt 1568 (.Swap ⟨4, by decide⟩),
   opAt 1569 .POP,
   opAt 1570 (.Dup ⟨3, by decide⟩),
   opAt 1571 .MSTORE,
   pushAt 1572 1 31,
   opAt 1573 .NOT,
   opAt 1574 .ADD,
   opAt 1575 (.Swap ⟨0, by decide⟩),
   pushAt 1576 1 31,
   opAt 1577 .NOT,
   opAt 1578 .ADD,
   opAt 1579 (.Swap ⟨0, by decide⟩),
   opAt 1580 (.Swap ⟨1, by decide⟩),
   pushAt 1581 1 31,
   opAt 1582 .NOT,
   opAt 1583 .ADD,
   opAt 1584 (.Swap ⟨1, by decide⟩),
   pushAt 1585 2 2080,
   opAt 1586 (.Dup ⟨1, by decide⟩),
   opAt 1587 .GT,
   pushAt 1588 2 2112,
   opAt 1589 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1590 .POP,
   opAt 1591 .POP,
   opAt 1592 .POP,
   opAt 1593 .ISZERO,
   pushAt 1594 2 2080,
   opAt 1595 .MLOAD,
   opAt 1596 .OR,
   pushAt 1597 2 319,
   opAt 1598 .NOT,
   opAt 1599 .MUL,
   pushAt 1600 2 2112,
   opAt 1601 .ADD,
   pushAt 1602 2 2688,
   opAt 1603 .MLOAD,
   opAt 1604 (.Swap ⟨1, by decide⟩),
   opAt 1605 .MCOPY,
   opAt 1606 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
