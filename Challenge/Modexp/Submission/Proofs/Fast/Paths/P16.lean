import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1781..1815).

`LZ` (pc 2560) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1781..1792, pc 2560..2937) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1793..1795, pc 2576..2943) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1796..1815, pc 2582..2970) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1781..1792, pc 2560..2937: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1589 .JUMPDEST,
   opAt 1590 (.Dup ⟨0, by decide⟩),
   pushAt 1591 2 2912,
   opAt 1592 .MLOAD,
   opAt 1593 .ADD,
   opAt 1594 .CALLDATALOAD,
   pushAt 1595 0 0,
   opAt 1596 .BYTE,
   opAt 1597 (.Dup ⟨1, by decide⟩),
   opAt 1598 .ISZERO,
   pushAt 1599 2 2165,
   opAt 1600 .JUMPI]

/-- Instructions 1793..1795, pc 2576..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1601 1 128,
   pushAt 1602 2 1519,
   opAt 1603 .JUMP]

/-- Instructions 1796..1815, pc 2582..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1604 .JUMPDEST,
   opAt 1605 (.Dup ⟨0, by decide⟩),
   opAt 1606 (.Dup ⟨0, by decide⟩),
   pushAt 1607 1 1,
   opAt 1608 .SHR,
   opAt 1609 .OR,
   opAt 1610 (.Dup ⟨0, by decide⟩),
   pushAt 1611 1 2,
   opAt 1612 .SHR,
   opAt 1613 .OR,
   opAt 1614 (.Dup ⟨0, by decide⟩),
   pushAt 1615 1 4,
   opAt 1616 .SHR,
   opAt 1617 .OR,
   pushAt 1618 1 1,
   opAt 1619 .SHR,
   pushAt 1620 1 1,
   opAt 1621 .ADD,
   pushAt 1622 2 3152,
   opAt 1623 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
