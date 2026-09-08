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
  [opAt 1446 .POP,
   opAt 1447 .POP,
   opAt 1448 (.Dup ⟨0, by decide⟩),
   pushAt 1449 2 8224,
   opAt 1450 .MLOAD,
   opAt 1451 .ADD,
   opAt 1452 (.Dup ⟨0, by decide⟩),
   pushAt 1453 2 8224,
   opAt 1454 .MSTORE,
   opAt 1455 .LT,
   pushAt 1456 2 8192,
   opAt 1457 .MSTORE,
   pushAt 1458 2 9440,
   opAt 1459 .MLOAD,
   opAt 1460 .MLOAD,
   pushAt 1461 2 9376,
   opAt 1462 .MLOAD,
   opAt 1463 .MUL,
   opAt 1464 (.Dup ⟨0, by decide⟩),
   pushAt 1465 2 9408,
   opAt 1466 .MLOAD,
   opAt 1467 .MLOAD,
   opAt 1468 (.Dup ⟨1, by decide⟩),
   opAt 1469 (.Dup ⟨1, by decide⟩),
   opAt 1470 .MUL,
   opAt 1471 (.Swap ⟨1, by decide⟩),
   pushAt 1472 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1473 (.Swap ⟨1, by decide⟩),
   opAt 1474 .MULMOD,
   opAt 1475 (.Dup ⟨1, by decide⟩),
   opAt 1476 (.Dup ⟨1, by decide⟩),
   opAt 1477 .LT,
   opAt 1478 (.Dup ⟨2, by decide⟩),
   opAt 1479 .ADD,
   opAt 1480 (.Swap ⟨0, by decide⟩),
   opAt 1481 .SUB,
   opAt 1482 (.Swap ⟨0, by decide⟩),
   pushAt 1483 0 0,
   opAt 1484 .LT,
   opAt 1485 .ADD,
   pushAt 1486 2 9440,
   opAt 1487 .MLOAD,
   pushAt 1488 1 32,
   opAt 1489 (.Swap ⟨0, by decide⟩),
   opAt 1490 .SUB,
   pushAt 1491 2 9408,
   opAt 1492 .MLOAD,
   pushAt 1493 1 32,
   opAt 1494 (.Swap ⟨0, by decide⟩),
   opAt 1495 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
