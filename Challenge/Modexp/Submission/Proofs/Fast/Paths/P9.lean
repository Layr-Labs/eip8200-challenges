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
  [opAt 1463 .POP,
   opAt 1464 .POP,
   opAt 1465 (.Dup ⟨0, by decide⟩),
   pushAt 1466 2 8224,
   opAt 1467 .MLOAD,
   opAt 1468 .ADD,
   opAt 1469 (.Dup ⟨0, by decide⟩),
   pushAt 1470 2 8224,
   opAt 1471 .MSTORE,
   opAt 1472 .LT,
   pushAt 1473 2 8192,
   opAt 1474 .MSTORE,
   pushAt 1475 2 9440,
   opAt 1476 .MLOAD,
   opAt 1477 .MLOAD,
   pushAt 1478 2 9376,
   opAt 1479 .MLOAD,
   opAt 1480 .MUL,
   opAt 1481 (.Dup ⟨0, by decide⟩),
   pushAt 1482 2 9408,
   opAt 1483 .MLOAD,
   opAt 1484 .MLOAD,
   opAt 1485 (.Dup ⟨1, by decide⟩),
   opAt 1486 (.Dup ⟨1, by decide⟩),
   opAt 1487 .MUL,
   opAt 1488 (.Swap ⟨1, by decide⟩),
   pushAt 1489 0 0, opAt 1490 .NOT,
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
