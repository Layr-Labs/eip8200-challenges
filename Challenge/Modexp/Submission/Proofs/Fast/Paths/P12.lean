import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1627..1682). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1627..1661, pc 2257..2634. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1508 .JUMPDEST,
   opAt 1509 (.Dup ⟨1, by decide⟩),
   opAt 1510 .MLOAD,
   opAt 1511 (.Dup ⟨3, by decide⟩),
   opAt 1512 .MLOAD,
   opAt 1513 (.Dup ⟨1, by decide⟩),
   opAt 1514 .ADD,
   opAt 1515 (.Swap ⟨0, by decide⟩),
   opAt 1516 (.Dup ⟨1, by decide⟩),
   opAt 1517 .LT,
   opAt 1518 (.Swap ⟨0, by decide⟩),
   opAt 1519 (.Dup ⟨5, by decide⟩),
   opAt 1520 .ADD,
   opAt 1521 (.Swap ⟨4, by decide⟩),
   opAt 1522 (.Dup ⟨5, by decide⟩),
   opAt 1523 .LT,
   opAt 1524 .OR,
   opAt 1525 (.Swap ⟨3, by decide⟩),
   opAt 1526 (.Dup ⟨1, by decide⟩),
   opAt 1527 .MSTORE,
   pushAt 1528 1 31,
   opAt 1529 .NOT,
   opAt 1530 .ADD,
   opAt 1531 (.Swap ⟨0, by decide⟩),
   pushAt 1532 1 31,
   opAt 1533 .NOT,
   opAt 1534 .ADD,
   opAt 1535 (.Swap ⟨0, by decide⟩),
   opAt 1536 (.Swap ⟨1, by decide⟩),
   pushAt 1537 1 31,
   opAt 1538 .NOT,
   opAt 1539 .ADD,
   opAt 1540 (.Swap ⟨1, by decide⟩),
   pushAt 1541 2 4128,
   opAt 1542 (.Dup ⟨1, by decide⟩),
   opAt 1543 .GT,
   pushAt 1544 2 2064,
   opAt 1545 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1546 .POP,
   opAt 1547 .POP,
   opAt 1548 .POP,
   pushAt 1549 2 4128,
   opAt 1550 .MSTORE,

   pushAt 1551 2 4804,
   opAt 1552 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
