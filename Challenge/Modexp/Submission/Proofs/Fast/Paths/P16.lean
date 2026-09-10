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
  [opAt 1775 .JUMPDEST,
   opAt 1776 (.Dup ⟨0, by decide⟩),
   pushAt 1777 2 9472,
   opAt 1778 .MLOAD,
   opAt 1779 .ADD,
   opAt 1780 .CALLDATALOAD,
   pushAt 1781 0 0,
   opAt 1782 .BYTE,
   opAt 1783 (.Dup ⟨1, by decide⟩),
   opAt 1784 .ISZERO,
   pushAt 1785 2 2577,
   opAt 1786 .JUMPI]

/-- Instructions 1793..1795, pc 2576..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1787 1 128,
   pushAt 1788 2 1789,
   opAt 1789 .JUMP]

/-- Instructions 1796..1815, pc 2582..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1790 .JUMPDEST,
   opAt 1791 (.Dup ⟨0, by decide⟩),
   opAt 1792 (.Dup ⟨0, by decide⟩),
   pushAt 1793 1 1,
   opAt 1794 .SHR,
   opAt 1795 .OR,
   opAt 1796 (.Dup ⟨0, by decide⟩),
   pushAt 1797 1 2,
   opAt 1798 .SHR,
   opAt 1799 .OR,
   opAt 1800 (.Dup ⟨0, by decide⟩),
   pushAt 1801 1 4,
   opAt 1802 .SHR,
   opAt 1803 .OR,
   pushAt 1804 1 1,
   opAt 1805 .SHR,
   pushAt 1806 1 1,
   opAt 1807 .ADD,
   pushAt 1808 2 3624,
   opAt 1809 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
