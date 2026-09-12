import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1752..1807). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1752..1786, pc 2378..2767. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1502 .JUMPDEST,
   opAt 1503 (.Dup ⟨1, by decide⟩),
   opAt 1504 .MLOAD,
   opAt 1505 (.Dup ⟨3, by decide⟩),
   opAt 1506 .MLOAD,
   opAt 1507 (.Dup ⟨1, by decide⟩),
   opAt 1508 .ADD,
   opAt 1509 (.Swap ⟨0, by decide⟩),
   opAt 1510 (.Dup ⟨1, by decide⟩),
   opAt 1511 .LT,
   opAt 1512 (.Swap ⟨0, by decide⟩),
   opAt 1513 (.Dup ⟨5, by decide⟩),
   opAt 1514 .ADD,
   opAt 1515 (.Swap ⟨4, by decide⟩),
   opAt 1516 (.Dup ⟨5, by decide⟩),
   opAt 1517 .LT,
   opAt 1518 .OR,
   opAt 1519 (.Swap ⟨3, by decide⟩),
   opAt 1520 (.Dup ⟨1, by decide⟩),
   opAt 1521 .MSTORE,
   pushAt 1522 1 31,
   opAt 1523 .NOT,
   opAt 1524 .ADD,
   opAt 1525 (.Swap ⟨0, by decide⟩),
   pushAt 1526 1 31,
   opAt 1527 .NOT,
   opAt 1528 .ADD,
   opAt 1529 (.Swap ⟨0, by decide⟩),
   opAt 1530 (.Swap ⟨1, by decide⟩),
   pushAt 1531 1 31,
   opAt 1532 .NOT,
   opAt 1533 .ADD,
   opAt 1534 (.Swap ⟨1, by decide⟩),
   pushAt 1535 2 4128,
   opAt 1536 (.Dup ⟨1, by decide⟩),
   opAt 1537 .GT,
   pushAt 1538 2 2054,
   opAt 1539 .JUMPI]

/-- Instructions 1792..1743, pc 2768..2429. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1540 .POP,
   opAt 1541 .POP,
   opAt 1542 .POP,
   pushAt 1543 2 4128,
   opAt 1544 .MSTORE,

   pushAt 1545 2 4875,
   opAt 1546 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
