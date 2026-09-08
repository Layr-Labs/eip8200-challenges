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
  [opAt 1467 .POP,
   opAt 1468 .POP,
   opAt 1469 (.Dup ⟨0, by decide⟩),
   pushAt 1470 2 8224,
   opAt 1471 .MLOAD,
   opAt 1472 .ADD,
   opAt 1473 (.Dup ⟨0, by decide⟩),
   pushAt 1474 2 8224,
   opAt 1475 .MSTORE,
   opAt 1476 .LT,
   pushAt 1477 2 8192,
   opAt 1478 .MSTORE,
   pushAt 1479 2 9440,
   opAt 1480 .MLOAD,
   opAt 1481 .MLOAD,
   pushAt 1482 2 9376,
   opAt 1483 .MLOAD,
   opAt 1484 .MUL,
   opAt 1485 (.Dup ⟨0, by decide⟩),
   pushAt 1486 2 9408,
   opAt 1487 .MLOAD,
   opAt 1488 .MLOAD,
   opAt 1489 (.Dup ⟨1, by decide⟩),
   opAt 1490 (.Dup ⟨1, by decide⟩),
   opAt 1491 .MUL,
   opAt 1492 (.Swap ⟨1, by decide⟩),
   pushAt 1493 0 0, opAt 1494 .NOT,
   opAt 1495 (.Swap ⟨1, by decide⟩),
   opAt 1496 .MULMOD,
   opAt 1497 (.Dup ⟨1, by decide⟩),
   opAt 1498 (.Dup ⟨1, by decide⟩),
   opAt 1499 .LT,
   opAt 1500 (.Dup ⟨2, by decide⟩),
   opAt 1501 .ADD,
   opAt 1502 (.Swap ⟨0, by decide⟩),
   opAt 1503 .SUB,
   opAt 1504 (.Swap ⟨0, by decide⟩),
   pushAt 1505 0 0,
   opAt 1506 .LT,
   opAt 1507 .ADD,
   pushAt 1508 2 9440,
   opAt 1509 .MLOAD,
   pushAt 1510 1 32,
   opAt 1511 (.Swap ⟨0, by decide⟩),
   opAt 1512 .SUB,
   pushAt 1513 2 9408,
   opAt 1514 .MLOAD,
   pushAt 1515 1 32,
   opAt 1516 (.Swap ⟨0, by decide⟩),
   opAt 1517 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
