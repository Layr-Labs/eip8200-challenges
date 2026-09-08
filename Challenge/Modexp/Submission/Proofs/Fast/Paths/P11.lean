import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1626). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1594, pc 2392..2459. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1569 .POP,
   opAt 1570 .POP,
   opAt 1571 (.Swap ⟨0, by decide⟩),
   opAt 1572 .POP,
   opAt 1573 (.Swap ⟨0, by decide⟩),
   opAt 1574 .POP,
   opAt 1575 (.Dup ⟨0, by decide⟩),
   pushAt 1576 2 8224,
   opAt 1577 .MLOAD,
   opAt 1578 .ADD,
   opAt 1579 (.Dup ⟨0, by decide⟩),
   pushAt 1580 2 8256,
   opAt 1581 .MSTORE,
   opAt 1582 .LT,
   pushAt 1583 2 8192,
   opAt 1584 .MLOAD,
   opAt 1585 .ADD,
   pushAt 1586 2 8224,
   opAt 1587 .MSTORE,
   pushAt 1588 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1589 .ADD,
   opAt 1590 (.Dup ⟨2, by decide⟩),
   opAt 1591 (.Dup ⟨1, by decide⟩),
   opAt 1592 .GT,
   pushAt 1593 2 1974,
   opAt 1594 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2466. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1595 .POP,
   opAt 1596 .POP,
   opAt 1597 .POP,
   pushAt 1598 2 2642,
   opAt 1599 .JUMP]

/-- Instructions 1600..1602, pc 2467..2471: trampoline to fused ADDMOD. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1600 .JUMPDEST,
   pushAt 1601 2 4569,
   opAt 1602 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
