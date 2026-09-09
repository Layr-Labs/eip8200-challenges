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
  [opAt 1514 .JUMPDEST,
   opAt 1515 (.Dup ⟨0, by decide⟩),
   opAt 1516 .MLOAD,
   pushAt 1517 0 0, opAt 1518 .NOT,
   opAt 1519 (.Dup ⟨5, by decide⟩),
   opAt 1520 (.Dup ⟨2, by decide⟩),
   opAt 1521 .MUL,
   opAt 1522 (.Swap ⟨1, by decide⟩),
   opAt 1523 (.Dup ⟨6, by decide⟩),
   opAt 1524 .MULMOD,
   opAt 1525 (.Dup ⟨1, by decide⟩),
   opAt 1526 (.Dup ⟨1, by decide⟩),
   opAt 1527 .LT,
   opAt 1528 .SUB,
   opAt 1529 (.Dup ⟨4, by decide⟩),
   opAt 1530 (.Dup ⟨2, by decide⟩),
   opAt 1531 .ADD,
   opAt 1532 (.Dup ⟨0, by decide⟩),
   opAt 1533 (.Swap ⟨5, by decide⟩),
   opAt 1534 .GT,
   opAt 1535 .SUB,
   opAt 1536 .SUB,
   opAt 1537 (.Dup ⟨3, by decide⟩),
   opAt 1538 (.Dup ⟨3, by decide⟩),
   opAt 1539 .MLOAD,
   opAt 1540 .ADD,
   opAt 1541 (.Dup ⟨0, by decide⟩),
   opAt 1542 (.Swap ⟨4, by decide⟩),
   opAt 1543 .GT,
   opAt 1544 .ADD,
   opAt 1545 (.Swap ⟨2, by decide⟩),
   pushAt 1546 1 32,
   opAt 1547 (.Dup ⟨3, by decide⟩),
   pushAt 1548 1 31, opAt 1549 .NOT,
   opAt 1550 .ADD,
   opAt 1551 (.Swap ⟨3, by decide⟩),
   opAt 1552 .ADD,
   opAt 1553 .MSTORE,
   pushAt 1554 1 31, opAt 1555 .NOT,
   opAt 1556 .ADD,
   pushAt 1557 2 8224,
   opAt 1558 (.Dup ⟨2, by decide⟩),
   opAt 1559 .GT,
   pushAt 1560 2 2119,
   opAt 1561 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
