import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1627..1682). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1627..1661, pc 2257..2634. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1532 .JUMPDEST,
   opAt 1533 (.Dup ⟨1, by decide⟩),
   opAt 1534 .MLOAD,
   opAt 1535 (.Dup ⟨3, by decide⟩),
   opAt 1536 .MLOAD,
   opAt 1537 (.Dup ⟨1, by decide⟩),
   opAt 1538 .ADD,
   opAt 1539 (.Swap ⟨0, by decide⟩),
   opAt 1540 (.Dup ⟨1, by decide⟩),
   opAt 1541 .LT,
   opAt 1542 (.Swap ⟨0, by decide⟩),
   opAt 1543 (.Dup ⟨5, by decide⟩),
   opAt 1544 .ADD,
   opAt 1545 (.Swap ⟨4, by decide⟩),
   opAt 1546 (.Dup ⟨5, by decide⟩),
   opAt 1547 .LT,
   opAt 1548 .OR,
   opAt 1549 (.Swap ⟨3, by decide⟩),
   opAt 1550 (.Dup ⟨1, by decide⟩),
   opAt 1551 .MSTORE,
   pushAt 1552 1 31,
   opAt 1553 .NOT,
   opAt 1554 .ADD,
   opAt 1555 (.Swap ⟨0, by decide⟩),
   pushAt 1556 1 31,
   opAt 1557 .NOT,
   opAt 1558 .ADD,
   opAt 1559 (.Swap ⟨0, by decide⟩),
   opAt 1560 (.Swap ⟨1, by decide⟩),
   pushAt 1561 1 31,
   opAt 1562 .NOT,
   opAt 1563 .ADD,
   opAt 1564 (.Swap ⟨1, by decide⟩),
   pushAt 1565 2 2080,
   opAt 1566 (.Dup ⟨1, by decide⟩),
   opAt 1567 .GT,
   pushAt 1568 2 2087,
   opAt 1569 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1570 .POP,
   opAt 1571 .POP,
   opAt 1572 .POP,
   pushAt 1573 2 2080,
   opAt 1574 .MSTORE,
   opAt 1575 .JUMPDEST,
   pushAt 1576 2 4902,
   opAt 1577 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
