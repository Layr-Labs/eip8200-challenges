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
  [opAt 1510 .JUMPDEST,
   opAt 1511 (.Dup ⟨0, by decide⟩),
   opAt 1512 .MLOAD,
   pushAt 1513 0 0, opAt 1514 .NOT,
   opAt 1515 (.Dup ⟨5, by decide⟩),
   opAt 1516 (.Dup ⟨2, by decide⟩),
   opAt 1517 .MUL,
   opAt 1518 (.Swap ⟨1, by decide⟩),
   opAt 1519 (.Dup ⟨6, by decide⟩),
   opAt 1520 .MULMOD,
   opAt 1521 (.Dup ⟨1, by decide⟩),
   opAt 1522 (.Dup ⟨1, by decide⟩),
   opAt 1523 .LT,
   opAt 1524 .SUB,
   opAt 1525 (.Dup ⟨4, by decide⟩),
   opAt 1526 (.Dup ⟨2, by decide⟩),
   opAt 1527 .ADD,
   opAt 1528 (.Dup ⟨0, by decide⟩),
   opAt 1529 (.Swap ⟨5, by decide⟩),
   opAt 1530 .GT,
   opAt 1531 .SUB,
   opAt 1532 .SUB,
   opAt 1533 (.Dup ⟨3, by decide⟩),
   opAt 1534 (.Dup ⟨3, by decide⟩),
   opAt 1535 .MLOAD,
   opAt 1536 .ADD,
   opAt 1537 (.Dup ⟨0, by decide⟩),
   opAt 1538 (.Swap ⟨4, by decide⟩),
   opAt 1539 .GT,
   opAt 1540 .ADD,
   opAt 1541 (.Swap ⟨2, by decide⟩),
   pushAt 1542 1 32,
   opAt 1543 (.Dup ⟨3, by decide⟩),
   pushAt 1544 1 31, opAt 1545 .NOT,
   opAt 1546 .ADD,
   opAt 1547 (.Swap ⟨3, by decide⟩),
   opAt 1548 .ADD,
   opAt 1549 .MSTORE,
   pushAt 1550 1 31, opAt 1551 .NOT,
   opAt 1552 .ADD,
   pushAt 1553 2 8224,
   opAt 1554 (.Dup ⟨2, by decide⟩),
   opAt 1555 .GT,
   pushAt 1556 2 2119,
   opAt 1557 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
