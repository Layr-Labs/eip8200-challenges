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
  [opAt 1459 .POP,
   opAt 1460 .POP,
   opAt 1461 (.Dup ⟨0, by decide⟩),
   pushAt 1462 2 8224,
   opAt 1463 .MLOAD,
   opAt 1464 .ADD,
   opAt 1465 (.Dup ⟨0, by decide⟩),
   pushAt 1466 2 8224,
   opAt 1467 .MSTORE,
   opAt 1468 .LT,
   pushAt 1469 2 8192,
   opAt 1470 .MSTORE,
   pushAt 1471 2 9440,
   opAt 1472 .MLOAD,
   opAt 1473 .MLOAD,
   pushAt 1474 2 9376,
   opAt 1475 .MLOAD,
   opAt 1476 .MUL,
   opAt 1477 (.Dup ⟨0, by decide⟩),
   pushAt 1478 2 9408,
   opAt 1479 .MLOAD,
   opAt 1480 .MLOAD,
   opAt 1481 (.Dup ⟨1, by decide⟩),
   opAt 1482 (.Dup ⟨1, by decide⟩),
   opAt 1483 .MUL,
   opAt 1484 (.Swap ⟨1, by decide⟩),
   pushAt 1485 0 0, opAt 1486 .NOT,
   opAt 1487 (.Swap ⟨1, by decide⟩),
   opAt 1488 .MULMOD,
   opAt 1489 (.Dup ⟨1, by decide⟩),
   opAt 1490 (.Dup ⟨1, by decide⟩),
   opAt 1491 .LT,
   opAt 1492 (.Dup ⟨2, by decide⟩),
   opAt 1493 .ADD,
   opAt 1494 (.Swap ⟨0, by decide⟩),
   opAt 1495 .SUB,
   opAt 1496 (.Swap ⟨0, by decide⟩),
   pushAt 1497 0 0,
   opAt 1498 .LT,
   opAt 1499 .ADD,
   pushAt 1500 2 9440,
   opAt 1501 .MLOAD,
   pushAt 1502 1 32,
   opAt 1503 (.Swap ⟨0, by decide⟩),
   opAt 1504 .SUB,
   pushAt 1505 2 9408,
   opAt 1506 .MLOAD,
   pushAt 1507 1 32,
   opAt 1508 (.Swap ⟨0, by decide⟩),
   opAt 1509 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
