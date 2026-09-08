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
  [opAt 1496 .JUMPDEST,
   opAt 1497 (.Dup ⟨0, by decide⟩),
   opAt 1498 .MLOAD,
   pushAt 1499 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1500 (.Dup ⟨5, by decide⟩),
   opAt 1501 (.Dup ⟨2, by decide⟩),
   opAt 1502 .MUL,
   opAt 1503 (.Swap ⟨1, by decide⟩),
   opAt 1504 (.Dup ⟨6, by decide⟩),
   opAt 1505 .MULMOD,
   opAt 1506 (.Dup ⟨1, by decide⟩),
   opAt 1507 (.Dup ⟨1, by decide⟩),
   opAt 1508 .LT,
   opAt 1509 .SUB,
   opAt 1510 (.Dup ⟨4, by decide⟩),
   opAt 1511 (.Dup ⟨2, by decide⟩),
   opAt 1512 .ADD,
   opAt 1513 (.Dup ⟨0, by decide⟩),
   opAt 1514 (.Swap ⟨5, by decide⟩),
   opAt 1515 .GT,
   opAt 1516 .SUB,
   opAt 1517 .SUB,
   opAt 1518 (.Dup ⟨3, by decide⟩),
   opAt 1519 (.Dup ⟨3, by decide⟩),
   opAt 1520 .MLOAD,
   opAt 1521 .ADD,
   opAt 1522 (.Dup ⟨0, by decide⟩),
   opAt 1523 (.Swap ⟨4, by decide⟩),
   opAt 1524 .GT,
   opAt 1525 .ADD,
   opAt 1526 (.Swap ⟨2, by decide⟩),
   pushAt 1527 1 32,
   opAt 1528 (.Dup ⟨3, by decide⟩),
   pushAt 1529 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1530 .ADD,
   opAt 1531 (.Swap ⟨3, by decide⟩),
   opAt 1532 .ADD,
   opAt 1533 .MSTORE,
   pushAt 1534 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1535 .ADD,
   pushAt 1536 2 8224,
   opAt 1537 (.Dup ⟨2, by decide⟩),
   opAt 1538 .GT,
   pushAt 1539 2 2104,
   opAt 1540 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
