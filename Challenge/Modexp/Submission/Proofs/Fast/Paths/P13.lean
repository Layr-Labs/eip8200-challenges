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
  [opAt 1501 .JUMPDEST,
   opAt 1502 (.Dup ⟨0, by decide⟩),
   opAt 1503 .MLOAD,
   opAt 1504 (.Dup ⟨2, by decide⟩),
   opAt 1505 .MLOAD,
   opAt 1506 (.Dup ⟨1, by decide⟩),
   opAt 1507 (.Dup ⟨1, by decide⟩),
   opAt 1508 .GT,
   opAt 1509 (.Swap ⟨1, by decide⟩),
   opAt 1510 .SUB,
   opAt 1511 (.Dup ⟨5, by decide⟩),
   opAt 1512 (.Dup ⟨1, by decide⟩),
   opAt 1513 .SUB,
   opAt 1514 (.Swap ⟨0, by decide⟩),
   opAt 1515 (.Dup ⟨6, by decide⟩),
   opAt 1516 .GT,
   opAt 1517 (.Swap ⟨0, by decide⟩),
   opAt 1518 (.Swap ⟨1, by decide⟩),
   opAt 1519 .OR,
   opAt 1520 (.Swap ⟨4, by decide⟩),
   opAt 1521 .POP,
   opAt 1522 (.Dup ⟨3, by decide⟩),
   opAt 1523 .MSTORE,
   pushAt 1524 1 31,
   opAt 1525 .NOT,
   opAt 1526 .ADD,
   opAt 1527 (.Swap ⟨0, by decide⟩),
   pushAt 1528 1 31,
   opAt 1529 .NOT,
   opAt 1530 .ADD,
   opAt 1531 (.Swap ⟨0, by decide⟩),
   opAt 1532 (.Swap ⟨1, by decide⟩),
   pushAt 1533 1 31,
   opAt 1534 .NOT,
   opAt 1535 .ADD,
   opAt 1536 (.Swap ⟨1, by decide⟩),
   pushAt 1537 2 2080,
   opAt 1538 (.Dup ⟨1, by decide⟩),
   opAt 1539 .GT,
   pushAt 1540 2 2026,
   opAt 1541 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1542 .POP,
   opAt 1543 .POP,
   opAt 1544 .POP,
   opAt 1545 .ISZERO,
   pushAt 1546 2 2080,
   opAt 1547 .MLOAD,
   opAt 1548 .OR,
   pushAt 1549 2 319,
   opAt 1550 .NOT,
   opAt 1551 .MUL,
   pushAt 1552 2 2112,
   opAt 1553 .ADD,
   pushAt 1554 2 2784,
   opAt 1555 .MLOAD,
   opAt 1556 (.Swap ⟨1, by decide⟩),
   opAt 1557 .MCOPY,
   opAt 1558 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
