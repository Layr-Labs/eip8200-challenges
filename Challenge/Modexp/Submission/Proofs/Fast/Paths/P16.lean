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
  [opAt 1565 .JUMPDEST,
   opAt 1566 (.Dup ⟨0, by decide⟩),
   pushAt 1567 2 5376,
   opAt 1568 .MLOAD,
   opAt 1569 .ADD,
   opAt 1570 .CALLDATALOAD,
   pushAt 1571 0 0,
   opAt 1572 .BYTE,
   opAt 1573 (.Dup ⟨1, by decide⟩),
   opAt 1574 .ISZERO,
   pushAt 1575 2 2124,
   opAt 1576 .JUMPI]

/-- Instructions 1793..1795, pc 2576..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1577 1 128,
   pushAt 1578 2 1486,
   opAt 1579 .JUMP]

/-- Instructions 1796..1815, pc 2582..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1580 .JUMPDEST,
   opAt 1581 (.Dup ⟨0, by decide⟩),
   opAt 1582 (.Dup ⟨0, by decide⟩),
   pushAt 1583 1 1,
   opAt 1584 .SHR,
   opAt 1585 .OR,
   opAt 1586 (.Dup ⟨0, by decide⟩),
   pushAt 1587 1 2,
   opAt 1588 .SHR,
   opAt 1589 .OR,
   opAt 1590 (.Dup ⟨0, by decide⟩),
   pushAt 1591 1 4,
   opAt 1592 .SHR,
   opAt 1593 .OR,
   pushAt 1594 1 1,
   opAt 1595 .SHR,
   pushAt 1596 1 1,
   opAt 1597 .ADD,
   pushAt 1598 2 3111,
   opAt 1599 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
