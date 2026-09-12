import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1757..1812). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1757..1791, pc 2384..2757. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1505 .JUMPDEST,
   opAt 1506 (.Dup ⟨1, by decide⟩),
   opAt 1507 .MLOAD,
   opAt 1508 (.Dup ⟨3, by decide⟩),
   opAt 1509 .MLOAD,
   opAt 1510 (.Dup ⟨1, by decide⟩),
   opAt 1511 .ADD,
   opAt 1512 (.Swap ⟨0, by decide⟩),
   opAt 1513 (.Dup ⟨1, by decide⟩),
   opAt 1514 .LT,
   opAt 1515 (.Swap ⟨0, by decide⟩),
   opAt 1516 (.Dup ⟨5, by decide⟩),
   opAt 1517 .ADD,
   opAt 1518 (.Swap ⟨4, by decide⟩),
   opAt 1519 (.Dup ⟨5, by decide⟩),
   opAt 1520 .LT,
   opAt 1521 .OR,
   opAt 1522 (.Swap ⟨3, by decide⟩),
   opAt 1523 (.Dup ⟨1, by decide⟩),
   opAt 1524 .MSTORE,
   pushAt 1525 1 31,
   opAt 1526 .NOT,
   opAt 1527 .ADD,
   opAt 1528 (.Swap ⟨0, by decide⟩),
   pushAt 1529 1 31,
   opAt 1530 .NOT,
   opAt 1531 .ADD,
   opAt 1532 (.Swap ⟨0, by decide⟩),
   opAt 1533 (.Swap ⟨1, by decide⟩),
   pushAt 1534 1 31,
   opAt 1535 .NOT,
   opAt 1536 .ADD,
   opAt 1537 (.Swap ⟨1, by decide⟩),
   pushAt 1538 2 4128,
   opAt 1539 (.Dup ⟨1, by decide⟩),
   opAt 1540 .GT,
   pushAt 1541 2 2059,
   opAt 1542 .JUMPI]

/-- Instructions 1792..1748, pc 2758..2435. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1543 .POP,
   opAt 1544 .POP,
   opAt 1545 .POP,
   pushAt 1546 2 4128,
   opAt 1547 .MSTORE,

   pushAt 1548 2 4874,
   opAt 1549 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
