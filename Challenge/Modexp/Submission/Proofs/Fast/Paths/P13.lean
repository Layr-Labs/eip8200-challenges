import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1683..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1683..1723, pc 2333..2473. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1475 .JUMPDEST,
   opAt 1476 (.Dup ⟨0, by decide⟩),
   opAt 1477 .MLOAD,
   opAt 1478 (.Dup ⟨2, by decide⟩),
   opAt 1479 .MLOAD,
   opAt 1480 (.Dup ⟨1, by decide⟩),
   opAt 1481 (.Dup ⟨1, by decide⟩),
   opAt 1482 .GT,
   opAt 1483 (.Swap ⟨1, by decide⟩),
   opAt 1484 .SUB,
   opAt 1485 (.Dup ⟨5, by decide⟩),
   opAt 1486 (.Dup ⟨1, by decide⟩),
   opAt 1487 .SUB,
   opAt 1488 (.Swap ⟨0, by decide⟩),
   opAt 1489 (.Dup ⟨6, by decide⟩),
   opAt 1490 .GT,
   opAt 1491 (.Swap ⟨0, by decide⟩),
   opAt 1492 (.Swap ⟨1, by decide⟩),
   opAt 1493 .OR,
   opAt 1494 (.Swap ⟨4, by decide⟩),
   opAt 1495 .POP,
   opAt 1496 (.Dup ⟨3, by decide⟩),
   opAt 1497 .MSTORE,
   pushAt 1498 1 31,
   opAt 1499 .NOT,
   opAt 1500 .ADD,
   opAt 1501 (.Swap ⟨0, by decide⟩),
   pushAt 1502 1 31,
   opAt 1503 .NOT,
   opAt 1504 .ADD,
   opAt 1505 (.Swap ⟨0, by decide⟩),
   opAt 1506 (.Swap ⟨1, by decide⟩),
   pushAt 1507 1 31,
   opAt 1508 .NOT,
   opAt 1509 .ADD,
   opAt 1510 (.Swap ⟨1, by decide⟩),
   pushAt 1511 2 8224,
   opAt 1512 (.Dup ⟨1, by decide⟩),
   opAt 1513 .GT,
   pushAt 1514 2 1981,
   opAt 1515 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1516 .POP,
   opAt 1517 .POP,
   opAt 1518 .POP,
   opAt 1519 .ISZERO,
   pushAt 1520 2 8224,
   opAt 1521 .MLOAD,
   opAt 1522 .OR,
   pushAt 1523 2 1087,
   opAt 1524 .NOT,
   opAt 1525 .MUL,
   pushAt 1526 2 8256,
   opAt 1527 .ADD,
   pushAt 1528 2 9344,
   opAt 1529 .MLOAD,
   opAt 1530 (.Swap ⟨1, by decide⟩),
   opAt 1531 .MCOPY,
   opAt 1532 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
