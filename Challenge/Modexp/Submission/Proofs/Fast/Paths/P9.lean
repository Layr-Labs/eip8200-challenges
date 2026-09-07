import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1469..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The landing `JUMPDEST` and the relocated P9 body, pc 2177..2264. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1493 .JUMPDEST,
   opAt 1494 .POP,
   opAt 1495 .POP,
   opAt 1496 (.Dup ⟨0, by decide⟩),
   pushAt 1497 2 8224,
   opAt 1498 .MLOAD,
   opAt 1499 .ADD,
   opAt 1500 (.Dup ⟨0, by decide⟩),
   pushAt 1501 2 8224,
   opAt 1502 .MSTORE,
   opAt 1503 .LT,
   pushAt 1504 2 8192,
   opAt 1505 .MSTORE,
   opAt 1506 (.Dup ⟨6, by decide⟩),
   opAt 1507 .MLOAD,
   opAt 1508 (.Dup ⟨0, by decide⟩),
   pushAt 1509 2 9376,
   opAt 1510 .MLOAD,
   opAt 1511 .MUL,
   opAt 1512 (.Swap ⟨0, by decide⟩),
   opAt 1513 (.Dup ⟨1, by decide⟩),
   pushAt 1514 2 9408,
   opAt 1515 .MLOAD,
   opAt 1516 .MLOAD,
   pushAt 1517 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1518 (.Swap ⟨1, by decide⟩),
   opAt 1519 .MULMOD,
   opAt 1520 (.Dup ⟨1, by decide⟩),
   opAt 1521 .ADD,
   opAt 1522 (.Dup ⟨0, by decide⟩),
   opAt 1523 (.Swap ⟨1, by decide⟩),
   opAt 1524 .GT,
   opAt 1525 .ADD,
   opAt 1526 (.Dup ⟨8, by decide⟩),
   pushAt 1527 1 32,
   opAt 1528 (.Swap ⟨0, by decide⟩),
   opAt 1529 .SUB,
   pushAt 1530 2 9408,
   opAt 1531 .MLOAD,
   pushAt 1532 1 32,
   opAt 1533 (.Swap ⟨0, by decide⟩),
   opAt 1534 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
