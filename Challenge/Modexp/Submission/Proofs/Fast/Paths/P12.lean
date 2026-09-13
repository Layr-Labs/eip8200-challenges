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
  [opAt 1499 .JUMPDEST,
   opAt 1500 (.Dup ⟨1, by decide⟩),
   opAt 1501 .MLOAD,
   opAt 1502 (.Dup ⟨3, by decide⟩),
   opAt 1503 .MLOAD,
   opAt 1504 (.Dup ⟨1, by decide⟩),
   opAt 1505 .ADD,
   opAt 1506 (.Swap ⟨0, by decide⟩),
   opAt 1507 (.Dup ⟨1, by decide⟩),
   opAt 1508 .LT,
   opAt 1509 (.Swap ⟨0, by decide⟩),
   opAt 1510 (.Dup ⟨5, by decide⟩),
   opAt 1511 .ADD,
   opAt 1512 (.Swap ⟨4, by decide⟩),
   opAt 1513 (.Dup ⟨5, by decide⟩),
   opAt 1514 .LT,
   opAt 1515 .OR,
   opAt 1516 (.Swap ⟨3, by decide⟩),
   opAt 1517 (.Dup ⟨1, by decide⟩),
   opAt 1518 .MSTORE,
   pushAt 1519 1 31,
   opAt 1520 .NOT,
   opAt 1521 .ADD,
   opAt 1522 (.Swap ⟨0, by decide⟩),
   pushAt 1523 1 31,
   opAt 1524 .NOT,
   opAt 1525 .ADD,
   opAt 1526 (.Swap ⟨0, by decide⟩),
   opAt 1527 (.Swap ⟨1, by decide⟩),
   pushAt 1528 1 31,
   opAt 1529 .NOT,
   opAt 1530 .ADD,
   opAt 1531 (.Swap ⟨1, by decide⟩),
   pushAt 1532 2 2080,
   opAt 1533 (.Dup ⟨1, by decide⟩),
   opAt 1534 .GT,
   pushAt 1535 2 2056,
   opAt 1536 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2416. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1537 .POP,
   opAt 1538 .POP,
   opAt 1539 .POP,
   pushAt 1540 2 2080,
   opAt 1541 .MSTORE,

   pushAt 1542 2 4877,
   opAt 1543 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
