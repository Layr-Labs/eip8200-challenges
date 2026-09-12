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
  [opAt 1641 .JUMPDEST,
   opAt 1642 (.Dup ⟨0, by decide⟩),
   pushAt 1643 2 5376,
   opAt 1644 .MLOAD,
   opAt 1645 .ADD,
   opAt 1646 .CALLDATALOAD,
   pushAt 1647 0 0,
   opAt 1648 .BYTE,
   opAt 1649 (.Dup ⟨1, by decide⟩),
   opAt 1650 .ISZERO,
   pushAt 1651 2 2259,
   opAt 1652 .JUMPI]

/-- Instructions 1793..1795, pc 2576..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1653 1 128,
   pushAt 1654 2 1621,
   opAt 1655 .JUMP]

/-- Instructions 1796..1815, pc 2582..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1656 .JUMPDEST,
   opAt 1657 (.Dup ⟨0, by decide⟩),
   opAt 1658 (.Dup ⟨0, by decide⟩),
   pushAt 1659 1 1,
   opAt 1660 .SHR,
   opAt 1661 .OR,
   opAt 1662 (.Dup ⟨0, by decide⟩),
   pushAt 1663 1 2,
   opAt 1664 .SHR,
   opAt 1665 .OR,
   opAt 1666 (.Dup ⟨0, by decide⟩),
   pushAt 1667 1 4,
   opAt 1668 .SHR,
   opAt 1669 .OR,
   pushAt 1670 1 1,
   opAt 1671 .SHR,
   pushAt 1672 1 1,
   opAt 1673 .ADD,
   pushAt 1674 2 3246,
   opAt 1675 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
