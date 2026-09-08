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
  [opAt 1509 .JUMPDEST,
   opAt 1510 (.Dup ⟨0, by decide⟩),
   opAt 1511 .MLOAD,
   pushAt 1512 0 0, opAt 1513 .NOT,
   opAt 1514 (.Dup ⟨5, by decide⟩),
   opAt 1515 (.Dup ⟨2, by decide⟩),
   opAt 1516 .MUL,
   opAt 1517 (.Swap ⟨1, by decide⟩),
   opAt 1518 (.Dup ⟨6, by decide⟩),
   opAt 1519 .MULMOD,
   opAt 1520 (.Dup ⟨1, by decide⟩),
   opAt 1521 (.Dup ⟨1, by decide⟩),
   opAt 1522 .LT,
   opAt 1523 .SUB,
   opAt 1524 (.Dup ⟨4, by decide⟩),
   opAt 1525 (.Dup ⟨2, by decide⟩),
   opAt 1526 .ADD,
   opAt 1527 (.Dup ⟨0, by decide⟩),
   opAt 1528 (.Swap ⟨5, by decide⟩),
   opAt 1529 .GT,
   opAt 1530 .SUB,
   opAt 1531 .SUB,
   opAt 1532 (.Dup ⟨3, by decide⟩),
   opAt 1533 (.Dup ⟨3, by decide⟩),
   opAt 1534 .MLOAD,
   opAt 1535 .ADD,
   opAt 1536 (.Dup ⟨0, by decide⟩),
   opAt 1537 (.Swap ⟨4, by decide⟩),
   opAt 1538 .GT,
   opAt 1539 .ADD,
   opAt 1540 (.Swap ⟨2, by decide⟩),
   pushAt 1541 1 32,
   opAt 1542 (.Dup ⟨3, by decide⟩),
   pushAt 1543 1 31, opAt 1544 .NOT,
   opAt 1545 .ADD,
   opAt 1546 (.Swap ⟨3, by decide⟩),
   opAt 1547 .ADD,
   opAt 1548 .MSTORE,
   pushAt 1549 1 31, opAt 1550 .NOT,
   opAt 1551 .ADD,
   pushAt 1552 2 8224,
   opAt 1553 (.Dup ⟨2, by decide⟩),
   opAt 1554 .GT,
   pushAt 1555 2 2110,
   opAt 1556 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
