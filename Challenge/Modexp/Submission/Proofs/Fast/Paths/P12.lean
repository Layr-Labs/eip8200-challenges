import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1627..1682). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1627..1661, pc 2257..2634. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1574 .JUMPDEST,
   opAt 1575 (.Dup ⟨1, by decide⟩),
   opAt 1576 .MLOAD,
   opAt 1577 (.Dup ⟨3, by decide⟩),
   opAt 1578 .MLOAD,
   opAt 1579 (.Dup ⟨1, by decide⟩),
   opAt 1580 .ADD,
   opAt 1581 (.Swap ⟨0, by decide⟩),
   opAt 1582 (.Dup ⟨1, by decide⟩),
   opAt 1583 .LT,
   opAt 1584 (.Swap ⟨0, by decide⟩),
   opAt 1585 (.Dup ⟨5, by decide⟩),
   opAt 1586 .ADD,
   opAt 1587 (.Swap ⟨4, by decide⟩),
   opAt 1588 (.Dup ⟨5, by decide⟩),
   opAt 1589 .LT,
   opAt 1590 .OR,
   opAt 1591 (.Swap ⟨3, by decide⟩),
   opAt 1592 (.Dup ⟨1, by decide⟩),
   opAt 1593 .MSTORE,
   pushAt 1594 1 31,
   opAt 1595 .NOT,
   opAt 1596 .ADD,
   opAt 1597 (.Swap ⟨0, by decide⟩),
   pushAt 1598 1 31,
   opAt 1599 .NOT,
   opAt 1600 .ADD,
   opAt 1601 (.Swap ⟨0, by decide⟩),
   opAt 1602 (.Swap ⟨1, by decide⟩),
   pushAt 1603 1 31,
   opAt 1604 .NOT,
   opAt 1605 .ADD,
   opAt 1606 (.Swap ⟨1, by decide⟩),
   pushAt 1607 2 8224,
   opAt 1608 (.Dup ⟨1, by decide⟩),
   opAt 1609 .GT,
   pushAt 1610 2 2168,
   opAt 1611 .JUMPI]

/-- Instructions 1662..1669, pc 2213..2224: the ADDMOD tail plus the CSUB
    trampoline hop to the real entry at 4976. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1612 .POP,
   opAt 1613 .POP,
   opAt 1614 .POP,
   pushAt 1615 2 8224,
   opAt 1616 .MSTORE,
   opAt 1617 .JUMPDEST,
   pushAt 1618 2 4976,
   opAt 1619 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
