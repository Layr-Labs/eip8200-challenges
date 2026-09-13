import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1908..1942).

`LZ` (pc 2695) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1908..1792, pc 2695..3071) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1790..1920, pc 2711..3077) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1875..1942, pc 2720..3189) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1908..1792, pc 2695..3071: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1633 .JUMPDEST,
   opAt 1634 (.Dup ⟨0, by decide⟩),
   pushAt 1635 2 2816,
   opAt 1636 .MLOAD,
   opAt 1637 .ADD,
   opAt 1638 .CALLDATALOAD,
   pushAt 1639 0 0,
   opAt 1640 .BYTE,
   opAt 1641 (.Dup ⟨1, by decide⟩),
   opAt 1642 .ISZERO,
   pushAt 1643 2 2251,
   opAt 1644 .JUMPI]

/-- Instructions 1790..1920, pc 2711..3077: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1645 1 128,
   pushAt 1646 2 1611,
   opAt 1647 .JUMP]

/-- Instructions 1875..1942, pc 2720..3189: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1648 .JUMPDEST,
   opAt 1649 (.Dup ⟨0, by decide⟩),
   opAt 1650 (.Dup ⟨0, by decide⟩),
   pushAt 1651 1 1,
   opAt 1652 .SHR,
   opAt 1653 .OR,
   opAt 1654 (.Dup ⟨0, by decide⟩),
   pushAt 1655 1 2,
   opAt 1656 .SHR,
   opAt 1657 .OR,
   opAt 1658 (.Dup ⟨0, by decide⟩),
   pushAt 1659 1 4,
   opAt 1660 .SHR,
   opAt 1661 .OR,
   pushAt 1662 1 1,
   opAt 1663 .SHR,
   pushAt 1664 1 1,
   opAt 1665 .ADD,
   pushAt 1666 2 3194,
   opAt 1667 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
