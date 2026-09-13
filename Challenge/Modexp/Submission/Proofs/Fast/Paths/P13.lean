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
  [opAt 1545 .JUMPDEST,
   opAt 1546 (.Dup ⟨0, by decide⟩),
   opAt 1547 .MLOAD,
   opAt 1548 (.Dup ⟨2, by decide⟩),
   opAt 1549 .MLOAD,
   opAt 1550 (.Dup ⟨1, by decide⟩),
   opAt 1551 (.Dup ⟨1, by decide⟩),
   opAt 1552 .GT,
   opAt 1553 (.Swap ⟨1, by decide⟩),
   opAt 1554 .SUB,
   opAt 1555 (.Dup ⟨5, by decide⟩),
   opAt 1556 (.Dup ⟨1, by decide⟩),
   opAt 1557 .SUB,
   opAt 1558 (.Swap ⟨0, by decide⟩),
   opAt 1559 (.Dup ⟨6, by decide⟩),
   opAt 1560 .GT,
   opAt 1561 (.Swap ⟨0, by decide⟩),
   opAt 1562 (.Swap ⟨1, by decide⟩),
   opAt 1563 .OR,
   opAt 1564 (.Swap ⟨4, by decide⟩),
   opAt 1565 .POP,
   opAt 1566 (.Dup ⟨3, by decide⟩),
   opAt 1567 .MSTORE,
   pushAt 1568 1 31,
   opAt 1569 .NOT,
   opAt 1570 .ADD,
   opAt 1571 (.Swap ⟨0, by decide⟩),
   pushAt 1572 1 31,
   opAt 1573 .NOT,
   opAt 1574 .ADD,
   opAt 1575 (.Swap ⟨0, by decide⟩),
   opAt 1576 (.Swap ⟨1, by decide⟩),
   pushAt 1577 1 31,
   opAt 1578 .NOT,
   opAt 1579 .ADD,
   opAt 1580 (.Swap ⟨1, by decide⟩),
   pushAt 1581 2 2080,
   opAt 1582 (.Dup ⟨1, by decide⟩),
   opAt 1583 .GT,
   pushAt 1584 2 2112,
   opAt 1585 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1586 .POP,
   opAt 1587 .POP,
   opAt 1588 .POP,
   opAt 1589 .ISZERO,
   pushAt 1590 2 2080,
   opAt 1591 .MLOAD,
   opAt 1592 .OR,
   pushAt 1593 2 319,
   opAt 1594 .NOT,
   opAt 1595 .MUL,
   pushAt 1596 2 2112,
   opAt 1597 .ADD,
   pushAt 1598 2 2688,
   opAt 1599 .MLOAD,
   opAt 1600 (.Swap ⟨1, by decide⟩),
   opAt 1601 .MCOPY,
   opAt 1602 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
