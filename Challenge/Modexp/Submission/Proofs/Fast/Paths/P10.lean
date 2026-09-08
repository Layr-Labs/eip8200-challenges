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
   opAt 1515 (.Dup ⟨0, by decide⟩),
   opAt 1516 .MLOAD,
   pushAt 1517 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1518 (.Dup ⟨5, by decide⟩),
   opAt 1519 (.Dup ⟨2, by decide⟩),
   opAt 1520 .MUL,
   opAt 1521 (.Swap ⟨1, by decide⟩),
   opAt 1522 (.Dup ⟨6, by decide⟩),
   opAt 1523 .MULMOD,
   opAt 1524 (.Dup ⟨1, by decide⟩),
   opAt 1525 (.Dup ⟨1, by decide⟩),
   opAt 1526 .LT,
   opAt 1527 .SUB,
   opAt 1528 (.Dup ⟨4, by decide⟩),
   opAt 1529 (.Dup ⟨2, by decide⟩),
   opAt 1530 .ADD,
   opAt 1531 (.Dup ⟨0, by decide⟩),
   opAt 1532 (.Swap ⟨5, by decide⟩),
   opAt 1533 .GT,
   opAt 1534 .SUB,
   opAt 1535 .SUB,
   opAt 1536 (.Dup ⟨3, by decide⟩),
   opAt 1537 (.Dup ⟨3, by decide⟩),
   opAt 1538 .MLOAD,
   opAt 1539 .ADD,
   opAt 1540 (.Dup ⟨0, by decide⟩),
   opAt 1541 (.Swap ⟨4, by decide⟩),
   opAt 1542 .GT,
   opAt 1543 .ADD,
   opAt 1544 (.Swap ⟨2, by decide⟩),
   pushAt 1545 1 32,
   opAt 1546 (.Dup ⟨3, by decide⟩),
   pushAt 1547 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1548 .ADD,
   opAt 1549 (.Swap ⟨3, by decide⟩),
   opAt 1550 .ADD,
   opAt 1551 .MSTORE,
   pushAt 1552 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1553 .ADD,
   pushAt 1554 2 8224,
   opAt 1555 (.Dup ⟨2, by decide⟩),
   opAt 1556 .GT,
   pushAt 1557 2 2241,
   opAt 1558 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
