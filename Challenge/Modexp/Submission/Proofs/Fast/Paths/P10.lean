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
  [opAt 1514 .JUMPDEST,
   opAt 1515 (.Dup ⟨3, by decide⟩),
   opAt 1516 (.Dup ⟨1, by decide⟩),
   opAt 1517 .MLOAD,
   opAt 1518 (.Dup ⟨1, by decide⟩),
   opAt 1519 (.Dup ⟨1, by decide⟩),
   opAt 1520 .MUL,
   opAt 1521 (.Swap ⟨1, by decide⟩),
   pushAt 1522 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1523 (.Swap ⟨1, by decide⟩),
   opAt 1524 .MULMOD,
   opAt 1525 (.Dup ⟨1, by decide⟩),
   opAt 1526 (.Dup ⟨1, by decide⟩),
   opAt 1527 .LT,
   opAt 1528 (.Dup ⟨2, by decide⟩),
   opAt 1529 .ADD,
   opAt 1530 (.Swap ⟨0, by decide⟩),
   opAt 1531 .SUB,
   opAt 1532 (.Dup ⟨3, by decide⟩),
   opAt 1533 .MLOAD,
   opAt 1534 (.Swap ⟨1, by decide⟩),
   opAt 1535 (.Dup ⟨2, by decide⟩),
   opAt 1536 .ADD,
   opAt 1537 (.Swap ⟨1, by decide⟩),
   opAt 1538 (.Dup ⟨2, by decide⟩),
   opAt 1539 .LT,
   opAt 1540 .ADD,
   opAt 1541 (.Swap ⟨0, by decide⟩),
   opAt 1542 (.Dup ⟨4, by decide⟩),
   opAt 1543 .ADD,
   opAt 1544 (.Swap ⟨3, by decide⟩),
   opAt 1545 (.Dup ⟨4, by decide⟩),
   opAt 1546 .LT,
   opAt 1547 .ADD,
   opAt 1548 (.Swap ⟨2, by decide⟩),
   opAt 1549 (.Dup ⟨2, by decide⟩),
   pushAt 1550 1 32,
   opAt 1551 .ADD,
   opAt 1552 .MSTORE,
   pushAt 1553 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1554 .ADD,
   opAt 1555 (.Swap ⟨0, by decide⟩),
   pushAt 1556 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1557 .ADD,
   opAt 1558 (.Swap ⟨0, by decide⟩),
   pushAt 1559 2 8224,
   opAt 1560 (.Dup ⟨2, by decide⟩),
   opAt 1561 .GT,
   pushAt 1562 2 2234,
   opAt 1563 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
