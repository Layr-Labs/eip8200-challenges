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
  [opAt 1640 .JUMPDEST,
   opAt 1641 (.Dup ⟨0, by decide⟩),
   pushAt 1642 2 9472,
   opAt 1643 .MLOAD,
   opAt 1644 .ADD,
   opAt 1645 .CALLDATALOAD,
   pushAt 1646 0 0,
   opAt 1647 .BYTE,
   opAt 1648 (.Dup ⟨1, by decide⟩),
   opAt 1649 .ISZERO,
   pushAt 1650 2 2259,
   opAt 1651 .JUMPI]

/-- Instructions 1793..1795, pc 2576..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1652 1 128,
   pushAt 1653 2 1621,
   opAt 1654 .JUMP]

/-- Instructions 1796..1815, pc 2582..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1655 .JUMPDEST,
   opAt 1656 (.Dup ⟨0, by decide⟩),
   opAt 1657 (.Dup ⟨0, by decide⟩),
   pushAt 1658 1 1,
   opAt 1659 .SHR,
   opAt 1660 .OR,
   opAt 1661 (.Dup ⟨0, by decide⟩),
   pushAt 1662 1 2,
   opAt 1663 .SHR,
   opAt 1664 .OR,
   opAt 1665 (.Dup ⟨0, by decide⟩),
   pushAt 1666 1 4,
   opAt 1667 .SHR,
   opAt 1668 .OR,
   pushAt 1669 1 1,
   opAt 1670 .SHR,
   pushAt 1671 1 1,
   opAt 1672 .ADD,
   pushAt 1673 2 3246,
   opAt 1674 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
