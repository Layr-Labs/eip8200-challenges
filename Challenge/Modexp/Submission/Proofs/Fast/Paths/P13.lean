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
  [opAt 1482 .JUMPDEST,
   opAt 1483 (.Dup ⟨0, by decide⟩),
   opAt 1484 .MLOAD,
   opAt 1485 (.Dup ⟨2, by decide⟩),
   opAt 1486 .MLOAD,
   opAt 1487 (.Dup ⟨1, by decide⟩),
   opAt 1488 (.Dup ⟨1, by decide⟩),
   opAt 1489 .GT,
   opAt 1490 (.Swap ⟨1, by decide⟩),
   opAt 1491 .SUB,
   opAt 1492 (.Dup ⟨5, by decide⟩),
   opAt 1493 (.Dup ⟨1, by decide⟩),
   opAt 1494 .SUB,
   opAt 1495 (.Swap ⟨0, by decide⟩),
   opAt 1496 (.Dup ⟨6, by decide⟩),
   opAt 1497 .GT,
   opAt 1498 (.Swap ⟨0, by decide⟩),
   opAt 1499 (.Swap ⟨1, by decide⟩),
   opAt 1500 .OR,
   opAt 1501 (.Swap ⟨4, by decide⟩),
   opAt 1502 .POP,
   opAt 1503 (.Dup ⟨3, by decide⟩),
   opAt 1504 .MSTORE,
   pushAt 1505 1 31,
   opAt 1506 .NOT,
   opAt 1507 .ADD,
   opAt 1508 (.Swap ⟨0, by decide⟩),
   pushAt 1509 1 31,
   opAt 1510 .NOT,
   opAt 1511 .ADD,
   opAt 1512 (.Swap ⟨0, by decide⟩),
   opAt 1513 (.Swap ⟨1, by decide⟩),
   pushAt 1514 1 31,
   opAt 1515 .NOT,
   opAt 1516 .ADD,
   opAt 1517 (.Swap ⟨1, by decide⟩),
   pushAt 1518 2 8224,
   opAt 1519 (.Dup ⟨1, by decide⟩),
   opAt 1520 .GT,
   pushAt 1521 2 1997,
   opAt 1522 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1523 .POP,
   opAt 1524 .POP,
   opAt 1525 .POP,
   opAt 1526 .ISZERO,
   pushAt 1527 2 8224,
   opAt 1528 .MLOAD,
   opAt 1529 .OR,
   pushAt 1530 2 1087,
   opAt 1531 .NOT,
   opAt 1532 .MUL,
   pushAt 1533 2 8256,
   opAt 1534 .ADD,
   pushAt 1535 2 9344,
   opAt 1536 .MLOAD,
   opAt 1537 (.Swap ⟨1, by decide⟩),
   opAt 1538 .MCOPY,
   opAt 1539 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
