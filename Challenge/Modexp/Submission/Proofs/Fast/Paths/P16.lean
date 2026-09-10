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
  [opAt 1667 .JUMPDEST,
   opAt 1668 (.Dup ⟨0, by decide⟩),
   pushAt 1669 2 9472,
   opAt 1670 .MLOAD,
   opAt 1671 .ADD,
   opAt 1672 .CALLDATALOAD,
   pushAt 1673 0 0,
   opAt 1674 .BYTE,
   opAt 1675 (.Dup ⟨1, by decide⟩),
   opAt 1676 .ISZERO,
   pushAt 1677 2 2284,
   opAt 1678 .JUMPI]

/-- Instructions 1793..1795, pc 2576..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1679 1 128,
   pushAt 1680 2 1634,
   opAt 1681 .JUMP]

/-- Instructions 1796..1815, pc 2582..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1682 .JUMPDEST,
   opAt 1683 (.Dup ⟨0, by decide⟩),
   opAt 1684 (.Dup ⟨0, by decide⟩),
   pushAt 1685 1 1,
   opAt 1686 .SHR,
   opAt 1687 .OR,
   opAt 1688 (.Dup ⟨0, by decide⟩),
   pushAt 1689 1 2,
   opAt 1690 .SHR,
   opAt 1691 .OR,
   opAt 1692 (.Dup ⟨0, by decide⟩),
   pushAt 1693 1 4,
   opAt 1694 .SHR,
   opAt 1695 .OR,
   pushAt 1696 1 1,
   opAt 1697 .SHR,
   pushAt 1698 1 1,
   opAt 1699 .ADD,
   pushAt 1700 2 3297,
   opAt 1701 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
