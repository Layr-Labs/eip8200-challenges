import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1590..1651). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The row-tail block, instructions 1596..1622, pc 2432..2497. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1596 .JUMPDEST,
   opAt 1597 .POP,
   opAt 1598 .POP,
   opAt 1599 (.Swap ⟨0, by decide⟩),
   opAt 1600 .POP,
   opAt 1601 (.Swap ⟨0, by decide⟩),
   opAt 1602 .POP,
   opAt 1603 (.Dup ⟨0, by decide⟩),
   pushAt 1604 2 8224,
   opAt 1605 .MLOAD,
   opAt 1606 .ADD,
   opAt 1607 (.Dup ⟨0, by decide⟩),
   pushAt 1608 2 8256,
   opAt 1609 .MSTORE,
   opAt 1610 .LT,
   pushAt 1611 2 8192,
   opAt 1612 .MLOAD,
   opAt 1613 .ADD,
   pushAt 1614 2 8224,
   opAt 1615 .MSTORE,
   pushAt 1616 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1617 .ADD,
   opAt 1618 (.Dup ⟨2, by decide⟩),
   opAt 1619 (.Dup ⟨1, by decide⟩),
   opAt 1620 .GT,
   pushAt 1621 2 2004,
   opAt 1622 .JUMPI]

/-- The final row cleanup, instructions 1623..1630, pc 2501..2510. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1623 .POP,
   opAt 1624 .POP,
   opAt 1625 .POP,
   opAt 1626 (.Swap ⟨1, by decide⟩),
   opAt 1627 .POP,
   opAt 1628 (.Swap ⟨0, by decide⟩),
   pushAt 1629 2 2686,
   opAt 1630 .JUMP]

/-- The CSUB continuation, instructions 1631..1657, pc 2511..2543. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1631 .JUMPDEST,
   pushAt 1632 2 9344,
   opAt 1633 .MLOAD,
   opAt 1634 (.Dup ⟨0, by decide⟩),
   opAt 1635 (.Dup ⟨2, by decide⟩),
   opAt 1636 .ADD,
   pushAt 1637 1 32,
   opAt 1638 (.Swap ⟨0, by decide⟩),
   opAt 1639 .SUB,
   opAt 1640 (.Dup ⟨1, by decide⟩),
   opAt 1641 (.Dup ⟨4, by decide⟩),
   opAt 1642 .ADD,
   pushAt 1643 1 32,
   opAt 1644 (.Swap ⟨0, by decide⟩),
   opAt 1645 .SUB,
   opAt 1646 (.Swap ⟨2, by decide⟩),
   opAt 1647 .POP,
   opAt 1648 (.Swap ⟨2, by decide⟩),
   opAt 1649 .POP,
   opAt 1650 .POP,
   pushAt 1651 2 9440,
   opAt 1652 .MLOAD,
   pushAt 1653 0 0,
   opAt 1654 .JUMPDEST,
   opAt 1655 .JUMPDEST,
   opAt 1656 (.Swap ⟨2, by decide⟩),
   opAt 1657 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
