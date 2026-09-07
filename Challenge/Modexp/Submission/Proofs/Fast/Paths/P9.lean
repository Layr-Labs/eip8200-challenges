import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1469..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1469..1518, pc 2141..2240. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1464 .POP,
   opAt 1465 .POP,
   opAt 1466 (.Dup ⟨0, by decide⟩),
   pushAt 1467 2 8224,
   opAt 1468 .MLOAD,
   opAt 1469 .ADD,
   opAt 1470 (.Dup ⟨0, by decide⟩),
   pushAt 1471 2 8224,
   opAt 1472 .MSTORE,
   opAt 1473 .LT,
   pushAt 1474 2 8192,
   opAt 1475 .MSTORE,
   pushAt 1476 2 9440,
   opAt 1477 .MLOAD,
   opAt 1478 .MLOAD,
   pushAt 1479 2 9376,
   opAt 1480 .MLOAD,
   opAt 1481 .MUL,
   opAt 1482 (.Dup ⟨0, by decide⟩),
   pushAt 1483 2 9408,
   opAt 1484 .MLOAD,
   opAt 1485 .MLOAD,
   opAt 1486 (.Dup ⟨1, by decide⟩),
   opAt 1487 (.Dup ⟨1, by decide⟩),
   opAt 1488 .MUL,
   opAt 1489 (.Swap ⟨1, by decide⟩),
   pushAt 1490 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1491 (.Swap ⟨1, by decide⟩),
   opAt 1492 .MULMOD,
   opAt 1493 (.Dup ⟨1, by decide⟩),
   opAt 1494 (.Dup ⟨1, by decide⟩),
   opAt 1495 .LT,
   opAt 1496 (.Dup ⟨2, by decide⟩),
   opAt 1497 .ADD,
   opAt 1498 (.Swap ⟨0, by decide⟩),
   opAt 1499 .SUB,
   opAt 1500 (.Swap ⟨0, by decide⟩),
   pushAt 1501 0 0,
   opAt 1502 .LT,
   opAt 1503 .ADD,
   pushAt 1504 2 9440,
   opAt 1505 .MLOAD,
   pushAt 1506 1 32,
   opAt 1507 (.Swap ⟨0, by decide⟩),
   opAt 1508 .SUB,
   pushAt 1509 2 9408,
   opAt 1510 .MLOAD,
   pushAt 1511 1 32,
   opAt 1512 (.Swap ⟨0, by decide⟩),
   opAt 1513 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
