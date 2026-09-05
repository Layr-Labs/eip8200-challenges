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
  [opAt 1470 .POP,
   opAt 1471 .POP,
   opAt 1472 (.Dup ⟨0, by decide⟩),
   pushAt 1473 2 8224,
   opAt 1474 .MLOAD,
   opAt 1475 .ADD,
   opAt 1476 (.Dup ⟨0, by decide⟩),
   pushAt 1477 2 8224,
   opAt 1478 .MSTORE,
   opAt 1479 .LT,
   pushAt 1480 2 8192,
   opAt 1481 .MSTORE,
   pushAt 1482 2 9440,
   opAt 1483 .MLOAD,
   opAt 1484 .MLOAD,
   pushAt 1485 2 9376,
   opAt 1486 .MLOAD,
   opAt 1487 .MUL,
   opAt 1488 (.Dup ⟨0, by decide⟩),
   pushAt 1489 2 9408,
   opAt 1490 .MLOAD,
   opAt 1491 .MLOAD,
   opAt 1492 (.Dup ⟨1, by decide⟩),
   opAt 1493 (.Dup ⟨1, by decide⟩),
   opAt 1494 .MUL,
   opAt 1495 (.Swap ⟨1, by decide⟩),
   pushAt 1496 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1497 (.Swap ⟨1, by decide⟩),
   opAt 1498 .MULMOD,
   opAt 1499 (.Dup ⟨1, by decide⟩),
   opAt 1500 (.Dup ⟨1, by decide⟩),
   opAt 1501 .LT,
   opAt 1502 (.Dup ⟨2, by decide⟩),
   opAt 1503 .ADD,
   opAt 1504 (.Swap ⟨0, by decide⟩),
   opAt 1505 .SUB,
   opAt 1506 (.Swap ⟨0, by decide⟩),
   pushAt 1507 0 0,
   opAt 1508 .LT,
   opAt 1509 .ADD,
   pushAt 1510 2 9440,
   opAt 1511 .MLOAD,
   pushAt 1512 1 32,
   opAt 1513 (.Swap ⟨0, by decide⟩),
   opAt 1514 .SUB,
   pushAt 1515 2 9408,
   opAt 1516 .MLOAD,
   pushAt 1517 1 32,
   opAt 1518 (.Swap ⟨0, by decide⟩),
   opAt 1519 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
