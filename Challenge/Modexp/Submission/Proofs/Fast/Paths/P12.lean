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
  [opAt 1507 .JUMPDEST,
   opAt 1508 (.Dup ⟨1, by decide⟩),
   opAt 1509 .MLOAD,
   opAt 1510 (.Dup ⟨3, by decide⟩),
   opAt 1511 .MLOAD,
   opAt 1512 (.Dup ⟨1, by decide⟩),
   opAt 1513 .ADD,
   opAt 1514 (.Swap ⟨0, by decide⟩),
   opAt 1515 (.Dup ⟨1, by decide⟩),
   opAt 1516 .LT,
   opAt 1517 (.Swap ⟨0, by decide⟩),
   opAt 1518 (.Dup ⟨5, by decide⟩),
   opAt 1519 .ADD,
   opAt 1520 (.Swap ⟨4, by decide⟩),
   opAt 1521 (.Dup ⟨5, by decide⟩),
   opAt 1522 .LT,
   opAt 1523 .OR,
   opAt 1524 (.Swap ⟨3, by decide⟩),
   opAt 1525 (.Dup ⟨1, by decide⟩),
   opAt 1526 .MSTORE,
   pushAt 1527 1 31,
   opAt 1528 .NOT,
   opAt 1529 .ADD,
   opAt 1530 (.Swap ⟨0, by decide⟩),
   pushAt 1531 1 31,
   opAt 1532 .NOT,
   opAt 1533 .ADD,
   opAt 1534 (.Swap ⟨0, by decide⟩),
   opAt 1535 (.Swap ⟨1, by decide⟩),
   pushAt 1536 1 31,
   opAt 1537 .NOT,
   opAt 1538 .ADD,
   opAt 1539 (.Swap ⟨1, by decide⟩),
   pushAt 1540 2 8224,
   opAt 1541 (.Dup ⟨1, by decide⟩),
   opAt 1542 .GT,
   pushAt 1543 2 2064,
   opAt 1544 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1545 .POP,
   opAt 1546 .POP,
   opAt 1547 .POP,
   pushAt 1548 2 8224,
   opAt 1549 .MSTORE,

   pushAt 1550 2 4804,
   opAt 1551 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
