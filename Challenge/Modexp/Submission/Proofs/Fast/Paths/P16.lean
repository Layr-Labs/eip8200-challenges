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
  [opAt 1774 .JUMPDEST,
   opAt 1775 (.Dup ⟨0, by decide⟩),
   pushAt 1776 2 9472,
   opAt 1777 .MLOAD,
   opAt 1778 .ADD,
   opAt 1779 .CALLDATALOAD,
   pushAt 1780 0 0,
   opAt 1781 .BYTE,
   opAt 1782 (.Dup ⟨1, by decide⟩),
   opAt 1783 .ISZERO,
   pushAt 1784 2 2557,
   opAt 1785 .JUMPI]

/-- Instructions 1793..1795, pc 2576..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1786 1 128,
   pushAt 1787 2 1780,
   opAt 1788 .JUMP]

/-- Instructions 1796..1815, pc 2582..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1789 .JUMPDEST,
   opAt 1790 (.Dup ⟨0, by decide⟩),
   opAt 1791 (.Dup ⟨0, by decide⟩),
   pushAt 1792 1 1,
   opAt 1793 .SHR,
   opAt 1794 .OR,
   opAt 1795 (.Dup ⟨0, by decide⟩),
   pushAt 1796 1 2,
   opAt 1797 .SHR,
   opAt 1798 .OR,
   opAt 1799 (.Dup ⟨0, by decide⟩),
   pushAt 1800 1 4,
   opAt 1801 .SHR,
   opAt 1802 .OR,
   pushAt 1803 1 1,
   opAt 1804 .SHR,
   pushAt 1805 1 1,
   opAt 1806 .ADD,
   pushAt 1807 2 3588,
   opAt 1808 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
