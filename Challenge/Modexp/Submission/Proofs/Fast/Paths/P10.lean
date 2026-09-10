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
  [opAt 1500 .JUMPDEST,
   opAt 1501 (.Dup ⟨0, by decide⟩),
   opAt 1502 .MLOAD,
   pushAt 1503 0 0,
   opAt 1504 .NOT,
   opAt 1505 (.Dup ⟨5, by decide⟩),
   opAt 1506 (.Dup ⟨2, by decide⟩),
   opAt 1507 .MUL,
   opAt 1508 (.Swap ⟨1, by decide⟩),
   opAt 1509 (.Dup ⟨6, by decide⟩),
   opAt 1510 .MULMOD,
   opAt 1511 (.Dup ⟨1, by decide⟩),
   opAt 1512 (.Dup ⟨1, by decide⟩),
   opAt 1513 .LT,
   opAt 1514 .SUB,
   opAt 1515 (.Dup ⟨4, by decide⟩),
   opAt 1516 (.Dup ⟨2, by decide⟩),
   opAt 1517 .ADD,
   opAt 1518 (.Dup ⟨0, by decide⟩),
   opAt 1519 (.Swap ⟨5, by decide⟩),
   opAt 1520 .GT,
   opAt 1521 .SUB,
   opAt 1522 .SUB,
   opAt 1523 (.Dup ⟨3, by decide⟩),
   opAt 1524 (.Dup ⟨3, by decide⟩),
   opAt 1525 .MLOAD,
   opAt 1526 .ADD,
   opAt 1527 (.Dup ⟨0, by decide⟩),
   opAt 1528 (.Swap ⟨4, by decide⟩),
   opAt 1529 .GT,
   opAt 1530 .ADD,
   opAt 1531 (.Swap ⟨2, by decide⟩),
   pushAt 1532 1 32,
   opAt 1533 (.Dup ⟨3, by decide⟩),
   pushAt 1534 1 31,
   opAt 1535 .NOT,
   opAt 1536 .ADD,
   opAt 1537 (.Swap ⟨3, by decide⟩),
   opAt 1538 .ADD,
   opAt 1539 .MSTORE,
   pushAt 1540 1 31,
   opAt 1541 .NOT,
   opAt 1542 .ADD,
   pushAt 1543 2 8224,
   opAt 1544 (.Dup ⟨2, by decide⟩),
   opAt 1545 .GT,
   pushAt 1546 2 2043,
   opAt 1547 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
