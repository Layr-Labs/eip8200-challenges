import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1519..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1519..1568, pc 2119..2178. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1512 .JUMPDEST,
   opAt 1513 (.Dup ⟨0, by decide⟩),
   opAt 1514 .MLOAD,
   pushAt 1515 0 0, opAt 1516 .NOT,
   opAt 1517 (.Dup ⟨5, by decide⟩),
   opAt 1518 (.Dup ⟨2, by decide⟩),
   opAt 1519 .MUL,
   opAt 1520 (.Swap ⟨1, by decide⟩),
   opAt 1521 (.Dup ⟨6, by decide⟩),
   opAt 1522 .MULMOD,
   opAt 1523 (.Dup ⟨1, by decide⟩),
   opAt 1524 (.Dup ⟨1, by decide⟩),
   opAt 1525 .LT,
   opAt 1526 .SUB,
   opAt 1527 (.Dup ⟨4, by decide⟩),
   opAt 1528 (.Dup ⟨2, by decide⟩),
   opAt 1529 .ADD,
   opAt 1530 (.Dup ⟨0, by decide⟩),
   opAt 1531 (.Swap ⟨5, by decide⟩),
   opAt 1532 .GT,
   opAt 1533 .SUB,
   opAt 1534 .SUB,
   opAt 1535 (.Dup ⟨3, by decide⟩),
   opAt 1536 (.Dup ⟨3, by decide⟩),
   opAt 1537 .MLOAD,
   opAt 1538 .ADD,
   opAt 1539 (.Dup ⟨0, by decide⟩),
   opAt 1540 (.Swap ⟨4, by decide⟩),
   opAt 1541 .GT,
   opAt 1542 .ADD,
   opAt 1543 (.Swap ⟨2, by decide⟩),
   pushAt 1544 1 32,
   opAt 1545 (.Dup ⟨3, by decide⟩),
   pushAt 1546 1 31, opAt 1547 .NOT,
   opAt 1548 .ADD,
   opAt 1549 (.Swap ⟨3, by decide⟩),
   opAt 1550 .ADD,
   opAt 1551 .MSTORE,
   pushAt 1552 1 31, opAt 1553 .NOT,
   opAt 1554 .ADD,
   pushAt 1555 2 8224,
   opAt 1556 (.Dup ⟨2, by decide⟩),
   opAt 1557 .GT,
   pushAt 1558 2 2103,
   opAt 1559 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
