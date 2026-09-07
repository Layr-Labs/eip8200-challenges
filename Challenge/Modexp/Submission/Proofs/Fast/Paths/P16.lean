import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1781..1815).

`LZ` (pc 2915) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1776..1787, pc 2915..2930) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1788..1790, pc 2931..2936) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1791..1810, pc 2937..2963) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1776..1787, pc 2915..2930: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1776 .JUMPDEST,
   opAt 1777 (.Dup ⟨0, by decide⟩),
   pushAt 1778 2 9472,
   opAt 1779 .MLOAD,
   opAt 1780 .ADD,
   opAt 1781 .CALLDATALOAD,
   pushAt 1782 0 0,
   opAt 1783 .BYTE,
   opAt 1784 (.Dup ⟨1, by decide⟩),
   opAt 1785 .ISZERO,
   pushAt 1786 2 2937,
   opAt 1787 .JUMPI]

/-- Instructions 1788..1790, pc 2931..2936: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1788 1 128,
   pushAt 1789 2 1789,
   opAt 1790 .JUMP]

/-- Instructions 1791..1810, pc 2937..2963: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1791 .JUMPDEST,
   opAt 1792 (.Dup ⟨0, by decide⟩),
   opAt 1793 (.Dup ⟨0, by decide⟩),
   pushAt 1794 1 1,
   opAt 1795 .SHR,
   opAt 1796 .OR,
   opAt 1797 (.Dup ⟨0, by decide⟩),
   pushAt 1798 1 2,
   opAt 1799 .SHR,
   opAt 1800 .OR,
   opAt 1801 (.Dup ⟨0, by decide⟩),
   pushAt 1802 1 4,
   opAt 1803 .SHR,
   opAt 1804 .OR,
   pushAt 1805 1 1,
   opAt 1806 .SHR,
   pushAt 1807 1 1,
   opAt 1808 .ADD,
   pushAt 1809 2 3858,
   opAt 1810 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
