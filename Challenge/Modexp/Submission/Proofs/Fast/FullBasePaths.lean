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
  [opAt 1544 .JUMPDEST,
   opAt 1545 (.Dup ⟨0, by decide⟩),
   opAt 1546 (.Dup ⟨3, by decide⟩),
   opAt 1547 .EQ,
   pushAt 1548 0 0,
   opAt 1549 .MLOAD,
   pushAt 1550 1 255,
   opAt 1551 .SHR,
   opAt 1552 .AND,
   opAt 1553 .ISZERO,
   pushAt 1554 2 2082,
   opAt 1555 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1556 (.Dup ⟨0, by decide⟩),
   pushAt 1557 1 96,
   pushAt 1558 2 256,
   opAt 1559 .CALLDATACOPY,
   pushAt 1560 2 2182,
   pushAt 1561 2 512,
   pushAt 1562 2 256,
   pushAt 1563 2 1536,
   pushAt 1564 2 3209,
   opAt 1565 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1566 .JUMPDEST,
   opAt 1567 (.Dup ⟨2, by decide⟩),
   pushAt 1568 1 31,
   opAt 1569 .ADD,
   pushAt 1570 1 5,
   opAt 1571 .SHR,
   opAt 1572 (.Dup ⟨3, by decide⟩),
   opAt 1573 (.Dup ⟨1, by decide⟩),
   pushAt 1574 1 5,
   opAt 1575 .SHL,
   opAt 1576 .SUB,
   pushAt 1577 1 3,
   opAt 1578 .SHL,
   pushAt 1579 1 96,
   opAt 1580 .CALLDATALOAD,
   opAt 1581 (.Swap ⟨0, by decide⟩),
   opAt 1582 .SHR,
   opAt 1583 (.Dup ⟨2, by decide⟩),
   pushAt 1584 1 224,
   opAt 1585 .ADD,
   opAt 1586 .MSTORE,
   pushAt 1587 1 1,
   pushAt 1588 2 864,
   opAt 1589 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
