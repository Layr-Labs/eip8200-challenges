import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1754..1809). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1754..1788, pc 2377..2769. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1500 .JUMPDEST,
   opAt 1501 (.Dup ⟨1, by decide⟩),
   opAt 1502 .MLOAD,
   opAt 1503 (.Dup ⟨3, by decide⟩),
   opAt 1504 .MLOAD,
   opAt 1505 (.Dup ⟨1, by decide⟩),
   opAt 1506 .ADD,
   opAt 1507 (.Swap ⟨0, by decide⟩),
   opAt 1508 (.Dup ⟨1, by decide⟩),
   opAt 1509 .LT,
   opAt 1510 (.Swap ⟨0, by decide⟩),
   opAt 1511 (.Dup ⟨5, by decide⟩),
   opAt 1512 .ADD,
   opAt 1513 (.Swap ⟨4, by decide⟩),
   opAt 1514 (.Dup ⟨5, by decide⟩),
   opAt 1515 .LT,
   opAt 1516 .OR,
   opAt 1517 (.Swap ⟨3, by decide⟩),
   opAt 1518 (.Dup ⟨1, by decide⟩),
   opAt 1519 .MSTORE,
   pushAt 1520 1 31,
   opAt 1521 .NOT,
   opAt 1522 .ADD,
   opAt 1523 (.Swap ⟨0, by decide⟩),
   pushAt 1524 1 31,
   opAt 1525 .NOT,
   opAt 1526 .ADD,
   opAt 1527 (.Swap ⟨0, by decide⟩),
   opAt 1528 (.Swap ⟨1, by decide⟩),
   pushAt 1529 1 31,
   opAt 1530 .NOT,
   opAt 1531 .ADD,
   opAt 1532 (.Swap ⟨1, by decide⟩),
   pushAt 1533 2 2080,
   opAt 1534 (.Dup ⟨1, by decide⟩),
   opAt 1535 .GT,
   pushAt 1536 2 2056,
   opAt 1537 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2416. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1538 .POP,
   opAt 1539 .POP,
   opAt 1540 .POP,
   pushAt 1541 2 2080,
   opAt 1542 .MSTORE,

   pushAt 1543 2 4877,
   opAt 1544 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
