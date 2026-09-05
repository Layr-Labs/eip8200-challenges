import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1519..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1519..1568, pc 2241..2391. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1520 .JUMPDEST,
   opAt 1521 (.Dup ⟨3, by decide⟩),
   opAt 1522 (.Dup ⟨1, by decide⟩),
   opAt 1523 .MLOAD,
   opAt 1524 (.Dup ⟨1, by decide⟩),
   opAt 1525 (.Dup ⟨1, by decide⟩),
   opAt 1526 .MUL,
   opAt 1527 (.Swap ⟨1, by decide⟩),
   pushAt 1528 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1529 (.Swap ⟨1, by decide⟩),
   opAt 1530 .MULMOD,
   opAt 1531 (.Dup ⟨1, by decide⟩),
   opAt 1532 (.Dup ⟨1, by decide⟩),
   opAt 1533 .LT,
   opAt 1534 (.Dup ⟨2, by decide⟩),
   opAt 1535 .ADD,
   opAt 1536 (.Swap ⟨0, by decide⟩),
   opAt 1537 .SUB,
   opAt 1538 (.Dup ⟨3, by decide⟩),
   opAt 1539 .MLOAD,
   opAt 1540 (.Swap ⟨1, by decide⟩),
   opAt 1541 (.Dup ⟨2, by decide⟩),
   opAt 1542 .ADD,
   opAt 1543 (.Swap ⟨1, by decide⟩),
   opAt 1544 (.Dup ⟨2, by decide⟩),
   opAt 1545 .LT,
   opAt 1546 .ADD,
   opAt 1547 (.Swap ⟨0, by decide⟩),
   opAt 1548 (.Dup ⟨4, by decide⟩),
   opAt 1549 .ADD,
   opAt 1550 (.Swap ⟨3, by decide⟩),
   opAt 1551 (.Dup ⟨4, by decide⟩),
   opAt 1552 .LT,
   opAt 1553 .ADD,
   opAt 1554 (.Swap ⟨2, by decide⟩),
   opAt 1555 (.Dup ⟨2, by decide⟩),
   pushAt 1556 1 32,
   opAt 1557 .ADD,
   opAt 1558 .MSTORE,
   pushAt 1559 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1560 .ADD,
   opAt 1561 (.Swap ⟨0, by decide⟩),
   pushAt 1562 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1563 .ADD,
   opAt 1564 (.Swap ⟨0, by decide⟩),
   pushAt 1565 2 8224,
   opAt 1566 (.Dup ⟨2, by decide⟩),
   opAt 1567 .GT,
   pushAt 1568 2 2241,
   opAt 1569 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
