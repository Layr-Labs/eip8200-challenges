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
  [opAt 1544 .JUMPDEST,
   opAt 1545 (.Dup ⟨0, by decide⟩),
   opAt 1546 .MLOAD,
   opAt 1547 (.Dup ⟨2, by decide⟩),
   opAt 1548 .MLOAD,
   opAt 1549 (.Dup ⟨1, by decide⟩),
   opAt 1550 (.Dup ⟨1, by decide⟩),
   opAt 1551 .GT,
   opAt 1552 (.Swap ⟨1, by decide⟩),
   opAt 1553 .SUB,
   opAt 1554 (.Dup ⟨5, by decide⟩),
   opAt 1555 (.Dup ⟨1, by decide⟩),
   opAt 1556 .SUB,
   opAt 1557 (.Swap ⟨0, by decide⟩),
   opAt 1558 (.Dup ⟨6, by decide⟩),
   opAt 1559 .GT,
   opAt 1560 (.Swap ⟨0, by decide⟩),
   opAt 1561 (.Swap ⟨1, by decide⟩),
   opAt 1562 .OR,
   opAt 1563 (.Swap ⟨4, by decide⟩),
   opAt 1564 .POP,
   opAt 1565 (.Dup ⟨3, by decide⟩),
   opAt 1566 .MSTORE,
   pushAt 1567 1 31,
   opAt 1568 .NOT,
   opAt 1569 .ADD,
   opAt 1570 (.Swap ⟨0, by decide⟩),
   pushAt 1571 1 31,
   opAt 1572 .NOT,
   opAt 1573 .ADD,
   opAt 1574 (.Swap ⟨0, by decide⟩),
   opAt 1575 (.Swap ⟨1, by decide⟩),
   pushAt 1576 1 31,
   opAt 1577 .NOT,
   opAt 1578 .ADD,
   opAt 1579 (.Swap ⟨1, by decide⟩),
   pushAt 1580 2 2080,
   opAt 1581 (.Dup ⟨1, by decide⟩),
   opAt 1582 .GT,
   pushAt 1583 2 2112,
   opAt 1584 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1585 .POP,
   opAt 1586 .POP,
   opAt 1587 .POP,
   opAt 1588 .ISZERO,
   pushAt 1589 2 2080,
   opAt 1590 .MLOAD,
   opAt 1591 .OR,
   pushAt 1592 2 319,
   opAt 1593 .NOT,
   opAt 1594 .MUL,
   pushAt 1595 2 2112,
   opAt 1596 .ADD,
   pushAt 1597 2 2688,
   opAt 1598 .MLOAD,
   opAt 1599 (.Swap ⟨1, by decide⟩),
   opAt 1600 .MCOPY,
   opAt 1601 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
