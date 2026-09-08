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
  [opAt 1458 .POP,
   opAt 1459 .POP,
   opAt 1460 (.Dup ⟨0, by decide⟩),
   pushAt 1461 2 8224,
   opAt 1462 .MLOAD,
   opAt 1463 .ADD,
   opAt 1464 (.Dup ⟨0, by decide⟩),
   pushAt 1465 2 8224,
   opAt 1466 .MSTORE,
   opAt 1467 .LT,
   pushAt 1468 2 8192,
   opAt 1469 .MSTORE,
   pushAt 1470 2 9440,
   opAt 1471 .MLOAD,
   opAt 1472 .MLOAD,
   pushAt 1473 2 9376,
   opAt 1474 .MLOAD,
   opAt 1475 .MUL,
   opAt 1476 (.Dup ⟨0, by decide⟩),
   pushAt 1477 2 9408,
   opAt 1478 .MLOAD,
   opAt 1479 .MLOAD,
   opAt 1480 (.Dup ⟨1, by decide⟩),
   opAt 1481 (.Dup ⟨1, by decide⟩),
   opAt 1482 .MUL,
   opAt 1483 (.Swap ⟨1, by decide⟩),
   pushAt 1484 0 0, opAt 1485 .NOT,
   opAt 1486 (.Swap ⟨1, by decide⟩),
   opAt 1487 .MULMOD,
   opAt 1488 (.Dup ⟨1, by decide⟩),
   opAt 1489 (.Dup ⟨1, by decide⟩),
   opAt 1490 .LT,
   opAt 1491 (.Dup ⟨2, by decide⟩),
   opAt 1492 .ADD,
   opAt 1493 (.Swap ⟨0, by decide⟩),
   opAt 1494 .SUB,
   opAt 1495 (.Swap ⟨0, by decide⟩),
   pushAt 1496 0 0,
   opAt 1497 .LT,
   opAt 1498 .ADD,
   pushAt 1499 2 9440,
   opAt 1500 .MLOAD,
   pushAt 1501 1 32,
   opAt 1502 (.Swap ⟨0, by decide⟩),
   opAt 1503 .SUB,
   pushAt 1504 2 9408,
   opAt 1505 .MLOAD,
   pushAt 1506 1 32,
   opAt 1507 (.Swap ⟨0, by decide⟩),
   opAt 1508 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
