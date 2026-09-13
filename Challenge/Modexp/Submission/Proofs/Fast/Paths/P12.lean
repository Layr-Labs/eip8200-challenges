import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1754..1809). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1754..1788, pc 2380..2769. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1504 .JUMPDEST,
   opAt 1505 (.Dup ⟨1, by decide⟩),
   opAt 1506 .MLOAD,
   opAt 1507 (.Dup ⟨3, by decide⟩),
   opAt 1508 .MLOAD,
   opAt 1509 (.Dup ⟨1, by decide⟩),
   opAt 1510 .ADD,
   opAt 1511 (.Swap ⟨0, by decide⟩),
   opAt 1512 (.Dup ⟨1, by decide⟩),
   opAt 1513 .LT,
   opAt 1514 (.Swap ⟨0, by decide⟩),
   opAt 1515 (.Dup ⟨5, by decide⟩),
   opAt 1516 .ADD,
   opAt 1517 (.Swap ⟨4, by decide⟩),
   opAt 1518 (.Dup ⟨5, by decide⟩),
   opAt 1519 .LT,
   opAt 1520 .OR,
   opAt 1521 (.Swap ⟨3, by decide⟩),
   opAt 1522 (.Dup ⟨1, by decide⟩),
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
   pushAt 1540 2 2056,
   opAt 1541 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2431. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1542 .POP,
   opAt 1543 .POP,
   opAt 1544 .POP,
   pushAt 1545 2 2080,
   opAt 1546 .MSTORE,

   pushAt 1547 2 4877,
   opAt 1548 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
