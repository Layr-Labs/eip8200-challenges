import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located paths for the full-width-base helper

The helper is appended after the fixed-window and direct-RR helpers. Its miss
path reproduces the original base-head computation before jumping to the
unchanged base loop at pc 1795.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1540 .JUMPDEST,
   opAt 1541 (.Dup ⟨0, by decide⟩),
   opAt 1542 (.Dup ⟨3, by decide⟩),
   opAt 1543 .EQ,
   pushAt 1544 0 0,
   opAt 1545 .MLOAD,
   pushAt 1546 1 255,
   opAt 1547 .SHR,
   opAt 1548 .AND,
   opAt 1549 .ISZERO,
   pushAt 1550 2 2082,
   opAt 1551 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1552 (.Dup ⟨0, by decide⟩),
   pushAt 1553 1 96,
   pushAt 1554 2 256,
   opAt 1555 .CALLDATACOPY,
   pushAt 1556 2 2182,
   pushAt 1557 2 512,
   pushAt 1558 2 256,
   pushAt 1559 2 1536,
   pushAt 1560 2 3209,
   opAt 1561 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1562 .JUMPDEST,
   opAt 1563 (.Dup ⟨2, by decide⟩),
   pushAt 1564 1 31,
   opAt 1565 .ADD,
   pushAt 1566 1 5,
   opAt 1567 .SHR,
   opAt 1568 (.Dup ⟨3, by decide⟩),
   opAt 1569 (.Dup ⟨1, by decide⟩),
   pushAt 1570 1 5,
   opAt 1571 .SHL,
   opAt 1572 .SUB,
   pushAt 1573 1 3,
   opAt 1574 .SHL,
   pushAt 1575 1 96,
   opAt 1576 .CALLDATALOAD,
   opAt 1577 (.Swap ⟨0, by decide⟩),
   opAt 1578 .SHR,
   opAt 1579 (.Dup ⟨2, by decide⟩),
   pushAt 1580 1 224,
   opAt 1581 .ADD,
   opAt 1582 .MSTORE,
   pushAt 1583 1 1,
   pushAt 1584 2 864,
   opAt 1585 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
