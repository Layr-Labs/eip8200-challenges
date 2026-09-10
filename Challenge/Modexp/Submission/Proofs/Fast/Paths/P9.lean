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
  [opAt 1461 .POP,
   opAt 1462 .POP,
   opAt 1463 (.Dup ⟨0, by decide⟩),
   pushAt 1464 2 8224,
   opAt 1465 .MLOAD,
   opAt 1466 .ADD,
   opAt 1467 (.Dup ⟨0, by decide⟩),
   pushAt 1468 2 8224,
   opAt 1469 .MSTORE,
   opAt 1470 .LT,
   pushAt 1471 2 8192,
   opAt 1472 .MSTORE,
   pushAt 1473 2 9440,
   opAt 1474 .MLOAD,
   opAt 1475 .MLOAD,
   pushAt 1476 2 9376,
   opAt 1477 .MLOAD,
   opAt 1478 .MUL,
   opAt 1479 (.Dup ⟨0, by decide⟩),
   pushAt 1480 2 9408,
   opAt 1481 .MLOAD,
   opAt 1482 .MLOAD,
   opAt 1483 (.Dup ⟨1, by decide⟩),
   opAt 1484 (.Dup ⟨1, by decide⟩),
   opAt 1485 .MUL,
   opAt 1486 (.Swap ⟨1, by decide⟩),
   pushAt 1487 0 0, opAt 1488 .NOT,
   opAt 1489 (.Swap ⟨1, by decide⟩),
   opAt 1490 .MULMOD,
   opAt 1491 (.Dup ⟨1, by decide⟩),
   opAt 1492 (.Dup ⟨1, by decide⟩),
   opAt 1493 .LT,
   opAt 1494 (.Dup ⟨2, by decide⟩),
   opAt 1495 .ADD,
   opAt 1496 (.Swap ⟨0, by decide⟩),
   opAt 1497 .SUB,
   opAt 1498 (.Swap ⟨0, by decide⟩),
   pushAt 1499 0 0,
   opAt 1500 .LT,
   opAt 1501 .ADD,
   pushAt 1502 2 9440,
   opAt 1503 .MLOAD,
   pushAt 1504 1 32,
   opAt 1505 (.Swap ⟨0, by decide⟩),
   opAt 1506 .SUB,
   pushAt 1507 2 9408,
   opAt 1508 .MLOAD,
   pushAt 1509 1 32,
   opAt 1510 (.Swap ⟨0, by decide⟩),
   opAt 1511 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
