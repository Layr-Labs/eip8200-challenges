import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1731..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1731..1771, pc 2333..2514. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1512 .JUMPDEST,
   opAt 1513 (.Dup ⟨0, by decide⟩),
   opAt 1514 .MLOAD,
   opAt 1515 (.Dup ⟨2, by decide⟩),
   opAt 1516 .MLOAD,
   opAt 1517 (.Dup ⟨1, by decide⟩),
   opAt 1518 (.Dup ⟨1, by decide⟩),
   opAt 1519 .GT,
   opAt 1520 (.Swap ⟨1, by decide⟩),
   opAt 1521 .SUB,
   opAt 1522 (.Dup ⟨5, by decide⟩),
   opAt 1523 (.Dup ⟨1, by decide⟩),
   opAt 1524 .SUB,
   opAt 1525 (.Swap ⟨0, by decide⟩),
   opAt 1526 (.Dup ⟨6, by decide⟩),
   opAt 1527 .GT,
   opAt 1528 (.Swap ⟨0, by decide⟩),
   opAt 1529 (.Swap ⟨1, by decide⟩),
   opAt 1530 .OR,
   opAt 1531 (.Swap ⟨4, by decide⟩),
   opAt 1532 .POP,
   opAt 1533 (.Dup ⟨3, by decide⟩),
   opAt 1534 .MSTORE,
   pushAt 1535 1 31,
   opAt 1536 .NOT,
   opAt 1537 .ADD,
   opAt 1538 (.Swap ⟨0, by decide⟩),
   pushAt 1539 1 31,
   opAt 1540 .NOT,
   opAt 1541 .ADD,
   opAt 1542 (.Swap ⟨0, by decide⟩),
   opAt 1543 (.Swap ⟨1, by decide⟩),
   pushAt 1544 1 31,
   opAt 1545 .NOT,
   opAt 1546 .ADD,
   opAt 1547 (.Swap ⟨1, by decide⟩),
   pushAt 1548 2 8224,
   opAt 1549 (.Dup ⟨1, by decide⟩),
   opAt 1550 .GT,
   pushAt 1551 2 2033,
   opAt 1552 .JUMPI]

/-- Live instructions 1772..1787, pc 2848..2901; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1553 .POP,
   opAt 1554 .POP,
   opAt 1555 .POP,
   opAt 1556 .ISZERO,
   pushAt 1557 2 8224,
   opAt 1558 .MLOAD,
   opAt 1559 .OR,
   pushAt 1560 2 1087,
   opAt 1561 .NOT,
   opAt 1562 .MUL,
   pushAt 1563 2 8256,
   opAt 1564 .ADD,
   pushAt 1565 2 9344,
   opAt 1566 .MLOAD,
   opAt 1567 (.Swap ⟨1, by decide⟩),
   opAt 1568 .MCOPY,
   opAt 1569 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
