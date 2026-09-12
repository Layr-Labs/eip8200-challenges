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
  [opAt 1570 .JUMPDEST,
   opAt 1571 (.Dup ⟨0, by decide⟩),
   pushAt 1572 2 9472,
   opAt 1573 .MLOAD,
   opAt 1574 .ADD,
   opAt 1575 .CALLDATALOAD,
   pushAt 1576 0 0,
   opAt 1577 .BYTE,
   opAt 1578 (.Dup ⟨1, by decide⟩),
   opAt 1579 .ISZERO,
   pushAt 1580 2 2136,
   opAt 1581 .JUMPI]

/-- Instructions 1793..1795, pc 2576..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1582 1 128,
   pushAt 1583 2 1498,
   opAt 1584 .JUMP]

/-- Instructions 1796..1815, pc 2582..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1585 .JUMPDEST,
   opAt 1586 (.Dup ⟨0, by decide⟩),
   opAt 1587 (.Dup ⟨0, by decide⟩),
   pushAt 1588 1 1,
   opAt 1589 .SHR,
   opAt 1590 .OR,
   opAt 1591 (.Dup ⟨0, by decide⟩),
   pushAt 1592 1 2,
   opAt 1593 .SHR,
   opAt 1594 .OR,
   opAt 1595 (.Dup ⟨0, by decide⟩),
   pushAt 1596 1 4,
   opAt 1597 .SHR,
   opAt 1598 .OR,
   pushAt 1599 1 1,
   opAt 1600 .SHR,
   pushAt 1601 1 1,
   opAt 1602 .ADD,
   pushAt 1603 2 3123,
   opAt 1604 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
