import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1781..1815).

`LZ` (pc 2922) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1781..1792, pc 2922..2937) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1793..1795, pc 2938..2943) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1796..1815, pc 2944..2970) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1781..1792, pc 2922..2937: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1778 .JUMPDEST,
   opAt 1779 (.Dup ⟨0, by decide⟩),
   pushAt 1780 2 9472,
   opAt 1781 .MLOAD,
   opAt 1782 .ADD,
   opAt 1783 .CALLDATALOAD,
   pushAt 1784 0 0,
   opAt 1785 .BYTE,
   opAt 1786 (.Dup ⟨1, by decide⟩),
   opAt 1787 .ISZERO,
   pushAt 1788 2 2729,
   opAt 1789 .JUMPI]

/-- Instructions 1793..1795, pc 2938..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1790 1 128,
   pushAt 1791 2 1789,
   opAt 1792 .JUMP]

/-- Instructions 1796..1815, pc 2944..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1793 .JUMPDEST,
   opAt 1794 (.Dup ⟨0, by decide⟩),
   opAt 1795 (.Dup ⟨0, by decide⟩),
   pushAt 1796 1 1,
   opAt 1797 .SHR,
   opAt 1798 .OR,
   opAt 1799 (.Dup ⟨0, by decide⟩),
   pushAt 1800 1 2,
   opAt 1801 .SHR,
   opAt 1802 .OR,
   opAt 1803 (.Dup ⟨0, by decide⟩),
   pushAt 1804 1 4,
   opAt 1805 .SHR,
   opAt 1806 .OR,
   pushAt 1807 1 1,
   opAt 1808 .SHR,
   pushAt 1809 1 1,
   opAt 1810 .ADD,
   pushAt 1811 2 3650,
   opAt 1812 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
