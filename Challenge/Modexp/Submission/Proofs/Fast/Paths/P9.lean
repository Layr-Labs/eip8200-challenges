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
  [opAt 1457 .POP,
   opAt 1458 .POP,
   opAt 1459 (.Dup ⟨0, by decide⟩),
   pushAt 1460 2 8224,
   opAt 1461 .MLOAD,
   opAt 1462 .ADD,
   opAt 1463 (.Dup ⟨0, by decide⟩),
   pushAt 1464 2 8224,
   opAt 1465 .MSTORE,
   opAt 1466 .LT,
   pushAt 1467 2 8192,
   opAt 1468 .MSTORE,
   pushAt 1469 2 9440,
   opAt 1470 .MLOAD,
   opAt 1471 .MLOAD,
   pushAt 1472 2 9376,
   opAt 1473 .MLOAD,
   opAt 1474 .MUL,
   opAt 1475 (.Dup ⟨0, by decide⟩),
   pushAt 1476 2 9408,
   opAt 1477 .MLOAD,
   opAt 1478 .MLOAD,
   opAt 1479 (.Dup ⟨1, by decide⟩),
   opAt 1480 (.Dup ⟨1, by decide⟩),
   opAt 1481 .MUL,
   opAt 1482 (.Swap ⟨1, by decide⟩),
   pushAt 1483 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1484 (.Swap ⟨1, by decide⟩),
   opAt 1485 .MULMOD,
   opAt 1486 (.Dup ⟨1, by decide⟩),
   opAt 1487 (.Dup ⟨1, by decide⟩),
   opAt 1488 .LT,
   opAt 1489 (.Dup ⟨2, by decide⟩),
   opAt 1490 .ADD,
   opAt 1491 (.Swap ⟨0, by decide⟩),
   opAt 1492 .SUB,
   opAt 1493 (.Swap ⟨0, by decide⟩),
   pushAt 1494 0 0,
   opAt 1495 .LT,
   opAt 1496 .ADD,
   pushAt 1497 2 9440,
   opAt 1498 .MLOAD,
   pushAt 1499 1 32,
   opAt 1500 (.Swap ⟨0, by decide⟩),
   opAt 1501 .SUB,
   pushAt 1502 2 9408,
   opAt 1503 .MLOAD,
   pushAt 1504 1 32,
   opAt 1505 (.Swap ⟨0, by decide⟩),
   opAt 1506 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
