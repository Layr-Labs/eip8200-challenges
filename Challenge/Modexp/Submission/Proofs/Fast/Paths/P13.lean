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
  [opAt 1477 .JUMPDEST,
   opAt 1478 (.Dup ⟨0, by decide⟩),
   opAt 1479 .MLOAD,
   opAt 1480 (.Dup ⟨2, by decide⟩),
   opAt 1481 .MLOAD,
   opAt 1482 (.Dup ⟨1, by decide⟩),
   opAt 1483 (.Dup ⟨1, by decide⟩),
   opAt 1484 .GT,
   opAt 1485 (.Swap ⟨1, by decide⟩),
   opAt 1486 .SUB,
   opAt 1487 (.Dup ⟨5, by decide⟩),
   opAt 1488 (.Dup ⟨1, by decide⟩),
   opAt 1489 .SUB,
   opAt 1490 (.Swap ⟨0, by decide⟩),
   opAt 1491 (.Dup ⟨6, by decide⟩),
   opAt 1492 .GT,
   opAt 1493 (.Swap ⟨0, by decide⟩),
   opAt 1494 (.Swap ⟨1, by decide⟩),
   opAt 1495 .OR,
   opAt 1496 (.Swap ⟨4, by decide⟩),
   opAt 1497 .POP,
   opAt 1498 (.Dup ⟨3, by decide⟩),
   opAt 1499 .MSTORE,
   pushAt 1500 1 31,
   opAt 1501 .NOT,
   opAt 1502 .ADD,
   opAt 1503 (.Swap ⟨0, by decide⟩),
   pushAt 1504 1 31,
   opAt 1505 .NOT,
   opAt 1506 .ADD,
   opAt 1507 (.Swap ⟨0, by decide⟩),
   opAt 1508 (.Swap ⟨1, by decide⟩),
   pushAt 1509 1 31,
   opAt 1510 .NOT,
   opAt 1511 .ADD,
   opAt 1512 (.Swap ⟨1, by decide⟩),
   pushAt 1513 2 4128,
   opAt 1514 (.Dup ⟨1, by decide⟩),
   opAt 1515 .GT,
   pushAt 1516 2 1985,
   opAt 1517 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1518 .POP,
   opAt 1519 .POP,
   opAt 1520 .POP,
   opAt 1521 .ISZERO,
   pushAt 1522 2 4128,
   opAt 1523 .MLOAD,
   opAt 1524 .OR,
   pushAt 1525 2 1087,
   opAt 1526 .NOT,
   opAt 1527 .MUL,
   pushAt 1528 2 4160,
   opAt 1529 .ADD,
   pushAt 1530 2 5248,
   opAt 1531 .MLOAD,
   opAt 1532 (.Swap ⟨1, by decide⟩),
   opAt 1533 .MCOPY,
   opAt 1534 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
