import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1519..1563). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1519..1563, pc 2241..2391. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1519 .JUMPDEST,
   opAt 1520 (.Dup ⟨0, by decide⟩),
   opAt 1521 .MLOAD,
   pushAt 1522 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1523 (.Dup ⟨5, by decide⟩),
   opAt 1524 (.Dup ⟨2, by decide⟩),
   opAt 1525 .MUL,
   opAt 1526 (.Swap ⟨1, by decide⟩),
   opAt 1527 (.Dup ⟨6, by decide⟩),
   opAt 1528 .MULMOD,
   opAt 1529 (.Dup ⟨1, by decide⟩),
   opAt 1530 (.Dup ⟨1, by decide⟩),
   opAt 1531 .LT,
   opAt 1532 .SUB,
   opAt 1533 (.Dup ⟨4, by decide⟩),
   opAt 1534 (.Dup ⟨2, by decide⟩),
   opAt 1535 .ADD,
   opAt 1536 (.Dup ⟨0, by decide⟩),
   opAt 1537 (.Swap ⟨5, by decide⟩),
   opAt 1538 .GT,
   opAt 1539 .SUB,
   opAt 1540 .SUB,
   opAt 1541 (.Dup ⟨3, by decide⟩),
   opAt 1542 (.Dup ⟨3, by decide⟩),
   opAt 1543 .MLOAD,
   opAt 1544 .ADD,
   opAt 1545 (.Dup ⟨0, by decide⟩),
   opAt 1546 (.Swap ⟨4, by decide⟩),
   opAt 1547 .GT,
   opAt 1548 .ADD,
   opAt 1549 (.Swap ⟨2, by decide⟩),
   pushAt 1550 1 32,
   opAt 1551 (.Dup ⟨3, by decide⟩),
   pushAt 1552 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1553 .ADD,
   opAt 1554 (.Swap ⟨3, by decide⟩),
   opAt 1555 .ADD,
   opAt 1556 .MSTORE,
   pushAt 1557 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1558 .ADD,
   pushAt 1559 2 8224,
   opAt 1560 (.Dup ⟨2, by decide⟩),
   opAt 1561 .GT,
   pushAt 1562 3 2241,
   opAt 1563 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
