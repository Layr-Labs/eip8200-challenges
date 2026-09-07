import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1469..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The landing `JUMPDEST` and the relocated P9 body, pc 2155..2235. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1480 .JUMPDEST,
   opAt 1481 .POP,
   opAt 1482 .POP,
   opAt 1483 (.Dup ⟨0, by decide⟩),
   pushAt 1484 2 8224,
   opAt 1485 .MLOAD,
   opAt 1486 .ADD,
   opAt 1487 (.Dup ⟨0, by decide⟩),
   pushAt 1488 2 8224,
   opAt 1489 .MSTORE,
   opAt 1490 .LT,
   pushAt 1491 2 8192,
   opAt 1492 .MSTORE,
   opAt 1493 (.Dup ⟨6, by decide⟩),
   opAt 1494 .MLOAD,
   pushAt 1495 2 9376,
   opAt 1496 .MLOAD,
   opAt 1497 .MUL,
   opAt 1498 (.Dup ⟨0, by decide⟩),
   pushAt 1499 2 9408,
   opAt 1500 .MLOAD,
   opAt 1501 .MLOAD,
   opAt 1502 (.Dup ⟨1, by decide⟩),
   opAt 1503 (.Dup ⟨1, by decide⟩),
   opAt 1504 .MUL,
   opAt 1505 (.Swap ⟨1, by decide⟩),
   pushAt 1506 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1507 (.Swap ⟨1, by decide⟩),
   opAt 1508 .MULMOD,
   opAt 1509 (.Dup ⟨1, by decide⟩),
   opAt 1510 (.Dup ⟨1, by decide⟩),
   opAt 1511 .LT,
   opAt 1512 (.Dup ⟨2, by decide⟩),
   opAt 1513 .ADD,
   opAt 1514 (.Swap ⟨0, by decide⟩),
   opAt 1515 .SUB,
   opAt 1516 (.Swap ⟨0, by decide⟩),
   pushAt 1517 0 0,
   opAt 1518 .LT,
   opAt 1519 .ADD,
   opAt 1520 (.Dup ⟨8, by decide⟩),
   pushAt 1521 1 32,
   opAt 1522 (.Swap ⟨0, by decide⟩),
   opAt 1523 .SUB,
   pushAt 1524 2 9408,
   opAt 1525 .MLOAD,
   pushAt 1526 1 32,
   opAt 1527 (.Swap ⟨0, by decide⟩),
   opAt 1528 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
