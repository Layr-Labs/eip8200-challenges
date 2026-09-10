import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1469..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1469..1518, pc 2050..2118. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1449 .POP,
   opAt 1450 .POP,
   opAt 1451 (.Dup ⟨0, by decide⟩),
   pushAt 1452 2 8224,
   opAt 1453 .MLOAD,
   opAt 1454 .ADD,
   opAt 1455 (.Dup ⟨0, by decide⟩),
   pushAt 1456 2 8224,
   opAt 1457 .MSTORE,
   opAt 1458 .LT,
   pushAt 1459 2 8192,
   opAt 1460 .MSTORE,
   pushAt 1461 2 9440,
   opAt 1462 .MLOAD,
   opAt 1463 .MLOAD,
   pushAt 1464 2 9376,
   opAt 1465 .MLOAD,
   opAt 1466 .MUL,
   opAt 1467 (.Dup ⟨0, by decide⟩),
   pushAt 1468 2 9408,
   opAt 1469 .MLOAD,
   opAt 1470 .MLOAD,
   opAt 1471 (.Dup ⟨1, by decide⟩),
   opAt 1472 (.Dup ⟨1, by decide⟩),
   opAt 1473 .MUL,
   opAt 1474 (.Swap ⟨1, by decide⟩),
   pushAt 1475 0 0,
   opAt 1476 .NOT,
   opAt 1477 (.Swap ⟨1, by decide⟩),
   opAt 1478 .MULMOD,
   opAt 1479 (.Dup ⟨1, by decide⟩),
   opAt 1480 (.Dup ⟨1, by decide⟩),
   opAt 1481 .LT,
   opAt 1482 (.Dup ⟨2, by decide⟩),
   opAt 1483 .ADD,
   opAt 1484 (.Swap ⟨0, by decide⟩),
   opAt 1485 .SUB,
   opAt 1486 (.Swap ⟨0, by decide⟩),
   pushAt 1487 0 0,
   opAt 1488 .LT,
   opAt 1489 .ADD,
   pushAt 1490 2 9440,
   opAt 1491 .MLOAD,
   pushAt 1492 1 32,
   opAt 1493 (.Swap ⟨0, by decide⟩),
   opAt 1494 .SUB,
   pushAt 1495 2 9408,
   opAt 1496 .MLOAD,
   pushAt 1497 1 32,
   opAt 1498 (.Swap ⟨0, by decide⟩),
   opAt 1499 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
