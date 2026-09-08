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
  [opAt 1507 .JUMPDEST,
   opAt 1508 (.Dup ⟨0, by decide⟩),
   opAt 1509 .MLOAD,
   pushAt 1510 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1511 (.Dup ⟨5, by decide⟩),
   opAt 1512 (.Dup ⟨2, by decide⟩),
   opAt 1513 .MUL,
   opAt 1514 (.Swap ⟨1, by decide⟩),
   opAt 1515 (.Dup ⟨6, by decide⟩),
   opAt 1516 .MULMOD,
   opAt 1517 (.Dup ⟨1, by decide⟩),
   opAt 1518 (.Dup ⟨1, by decide⟩),
   opAt 1519 .LT,
   opAt 1520 .SUB,
   opAt 1521 (.Dup ⟨4, by decide⟩),
   opAt 1522 (.Dup ⟨2, by decide⟩),
   opAt 1523 .ADD,
   opAt 1524 (.Dup ⟨0, by decide⟩),
   opAt 1525 (.Swap ⟨5, by decide⟩),
   opAt 1526 .GT,
   opAt 1527 .SUB,
   opAt 1528 .SUB,
   opAt 1529 (.Dup ⟨3, by decide⟩),
   opAt 1530 (.Dup ⟨3, by decide⟩),
   opAt 1531 .MLOAD,
   opAt 1532 .ADD,
   opAt 1533 (.Dup ⟨0, by decide⟩),
   opAt 1534 (.Swap ⟨4, by decide⟩),
   opAt 1535 .GT,
   opAt 1536 .ADD,
   opAt 1537 (.Swap ⟨2, by decide⟩),
   pushAt 1538 1 32,
   opAt 1539 (.Dup ⟨3, by decide⟩),
   pushAt 1540 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1541 .ADD,
   opAt 1542 (.Swap ⟨3, by decide⟩),
   opAt 1543 .ADD,
   opAt 1544 .MSTORE,
   pushAt 1545 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1546 .ADD,
   pushAt 1547 2 8224,
   opAt 1548 (.Dup ⟨2, by decide⟩),
   opAt 1549 .GT,
   pushAt 1550 2 2217,
   opAt 1551 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
