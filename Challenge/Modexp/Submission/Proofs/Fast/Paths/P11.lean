import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1626). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1594, pc 2179..2459. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1476 .POP,
   opAt 1477 .POP,
   opAt 1478 (.Swap ⟨1, by decide⟩),
   opAt 1479 .POP,
   opAt 1480 .POP,
   opAt 1481 (.Dup ⟨0, by decide⟩),
   pushAt 1482 2 8224,
   opAt 1483 .MLOAD,
   opAt 1484 .ADD,
   opAt 1485 (.Dup ⟨0, by decide⟩),
   pushAt 1486 2 8256,
   opAt 1487 .MSTORE,
   opAt 1488 .LT,
   pushAt 1489 2 8192,
   opAt 1490 .MLOAD,
   opAt 1491 .ADD,
   pushAt 1492 2 8224,
   opAt 1493 .MSTORE,
   pushAt 1494 1 31,
   opAt 1495 .NOT,
   opAt 1496 .ADD,
   opAt 1497 (.Dup ⟨2, by decide⟩),
   opAt 1498 (.Dup ⟨1, by decide⟩),
   opAt 1499 .GT,
   pushAt 1500 2 1819,
   opAt 1501 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1502 .POP,
   opAt 1503 .POP,
   opAt 1504 .POP,
   pushAt 1505 2 2139,
   opAt 1506 .JUMP]

/-- Instructions 1507..1531, pc 2056..2086. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1507 .JUMPDEST,
   pushAt 1508 2 9344,
   opAt 1509 .MLOAD,
   pushAt 1510 1 31,
   opAt 1511 .NOT,
   opAt 1512 .ADD,
   opAt 1513 (.Dup ⟨0, by decide⟩),
   opAt 1514 (.Swap ⟨1, by decide⟩),
   opAt 1515 .ADD,
   opAt 1516 (.Swap ⟨1, by decide⟩),
   opAt 1517 .ADD,
   opAt 1518 .JUMPDEST,
   opAt 1519 .JUMPDEST,
   opAt 1520 .JUMPDEST,
   opAt 1521 .JUMPDEST,
   opAt 1522 .JUMPDEST,
   opAt 1523 .JUMPDEST,
   opAt 1524 .JUMPDEST,
   pushAt 1525 1 0,
   opAt 1526 .POP,
   pushAt 1527 2 9440,
   opAt 1528 .MLOAD,
   pushAt 1529 0 0,
   opAt 1530 (.Swap ⟨2, by decide⟩),
   opAt 1531 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
