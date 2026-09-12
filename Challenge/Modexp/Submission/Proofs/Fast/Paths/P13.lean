import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1808..1818). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1808..1848, pc 2409..2606. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1547 .JUMPDEST,
   opAt 1548 (.Dup ⟨0, by decide⟩),
   opAt 1549 .MLOAD,
   opAt 1550 (.Dup ⟨2, by decide⟩),
   opAt 1551 .MLOAD,
   opAt 1552 (.Dup ⟨1, by decide⟩),
   opAt 1553 (.Dup ⟨1, by decide⟩),
   opAt 1554 .GT,
   opAt 1555 (.Swap ⟨1, by decide⟩),
   opAt 1556 .SUB,
   opAt 1557 (.Dup ⟨5, by decide⟩),
   opAt 1558 (.Dup ⟨1, by decide⟩),
   opAt 1559 .SUB,
   opAt 1560 (.Swap ⟨0, by decide⟩),
   opAt 1561 (.Dup ⟨6, by decide⟩),
   opAt 1562 .GT,
   opAt 1563 (.Swap ⟨0, by decide⟩),
   opAt 1564 (.Swap ⟨1, by decide⟩),
   opAt 1565 .OR,
   opAt 1566 (.Swap ⟨4, by decide⟩),
   opAt 1567 .POP,
   opAt 1568 (.Dup ⟨3, by decide⟩),
   opAt 1569 .MSTORE,
   pushAt 1570 1 31,
   opAt 1571 .NOT,
   opAt 1572 .ADD,
   opAt 1573 (.Swap ⟨0, by decide⟩),
   pushAt 1574 1 31,
   opAt 1575 .NOT,
   opAt 1576 .ADD,
   opAt 1577 (.Swap ⟨0, by decide⟩),
   opAt 1578 (.Swap ⟨1, by decide⟩),
   pushAt 1579 1 31,
   opAt 1580 .NOT,
   opAt 1581 .ADD,
   opAt 1582 (.Swap ⟨1, by decide⟩),
   pushAt 1583 2 4128,
   opAt 1584 (.Dup ⟨1, by decide⟩),
   opAt 1585 .GT,
   pushAt 1586 2 2110,
   opAt 1587 .JUMPI]

/-- Live instructions 1849..1864, pc 2848..2993; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1588 .POP,
   opAt 1589 .POP,
   opAt 1590 .POP,
   opAt 1591 .ISZERO,
   pushAt 1592 2 4128,
   opAt 1593 .MLOAD,
   opAt 1594 .OR,
   pushAt 1595 2 1087,
   opAt 1596 .NOT,
   opAt 1597 .MUL,
   pushAt 1598 2 4160,
   opAt 1599 .ADD,
   pushAt 1600 2 5248,
   opAt 1601 .MLOAD,
   opAt 1602 (.Swap ⟨1, by decide⟩),
   opAt 1603 .MCOPY,
   opAt 1604 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
