import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1829..1863).

`LZ` (pc 2601) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1829..1792, pc 2601..2978) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1793..1843, pc 2617..2984) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1796..1863, pc 2623..3011) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1829..1792, pc 2601..2978: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1600 .JUMPDEST,
   opAt 1601 (.Dup ⟨0, by decide⟩),
   pushAt 1602 2 9472,
   opAt 1603 .MLOAD,
   opAt 1604 .ADD,
   opAt 1605 .CALLDATALOAD,
   pushAt 1606 0 0,
   opAt 1607 .BYTE,
   opAt 1608 (.Dup ⟨1, by decide⟩),
   opAt 1609 .ISZERO,
   pushAt 1610 2 2172,
   opAt 1611 .JUMPI]

/-- Instructions 1793..1843, pc 2617..2984: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1612 1 128,
   pushAt 1613 2 1534,
   opAt 1614 .JUMP]

/-- Instructions 1796..1863, pc 2623..3011: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1615 .JUMPDEST,
   opAt 1616 (.Dup ⟨0, by decide⟩),
   opAt 1617 (.Dup ⟨0, by decide⟩),
   pushAt 1618 1 1,
   opAt 1619 .SHR,
   opAt 1620 .OR,
   opAt 1621 (.Dup ⟨0, by decide⟩),
   pushAt 1622 1 2,
   opAt 1623 .SHR,
   opAt 1624 .OR,
   opAt 1625 (.Dup ⟨0, by decide⟩),
   pushAt 1626 1 4,
   opAt 1627 .SHR,
   opAt 1628 .OR,
   pushAt 1629 1 1,
   opAt 1630 .SHR,
   pushAt 1631 1 1,
   opAt 1632 .ADD,
   pushAt 1633 2 3152,
   opAt 1634 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
