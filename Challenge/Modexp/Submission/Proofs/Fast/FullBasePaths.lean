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
  [opAt 1542 .JUMPDEST,
   opAt 1543 (.Dup ⟨0, by decide⟩),
   opAt 1544 (.Dup ⟨3, by decide⟩),
   opAt 1545 .EQ,
   pushAt 1546 0 0,
   opAt 1547 .MLOAD,
   pushAt 1548 1 255,
   opAt 1549 .SHR,
   opAt 1550 .AND,
   opAt 1551 .ISZERO,
   pushAt 1552 2 2082,
   opAt 1553 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1554 (.Dup ⟨0, by decide⟩),
   pushAt 1555 1 96,
   pushAt 1556 2 256,
   opAt 1557 .CALLDATACOPY,
   pushAt 1558 2 2182,
   pushAt 1559 2 512,
   pushAt 1560 2 256,
   pushAt 1561 2 1536,
   pushAt 1562 2 3209,
   opAt 1563 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1564 .JUMPDEST,
   opAt 1565 (.Dup ⟨2, by decide⟩),
   pushAt 1566 1 31,
   opAt 1567 .ADD,
   pushAt 1568 1 5,
   opAt 1569 .SHR,
   opAt 1570 (.Dup ⟨3, by decide⟩),
   opAt 1571 (.Dup ⟨1, by decide⟩),
   pushAt 1572 1 5,
   opAt 1573 .SHL,
   opAt 1574 .SUB,
   pushAt 1575 1 3,
   opAt 1576 .SHL,
   pushAt 1577 1 96,
   opAt 1578 .CALLDATALOAD,
   opAt 1579 (.Swap ⟨0, by decide⟩),
   opAt 1580 .SHR,
   opAt 1581 (.Dup ⟨2, by decide⟩),
   pushAt 1582 1 224,
   opAt 1583 .ADD,
   opAt 1584 .MSTORE,
   pushAt 1585 1 1,
   pushAt 1586 2 864,
   opAt 1587 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
