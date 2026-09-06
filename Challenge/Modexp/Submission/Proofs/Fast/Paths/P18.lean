import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 18 (instructions 1831..1845).

`LZBASE` (pc 3000) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk1831` (idx 1831..1835, pc 3000..3006) — the `w = 0` test;
* `blk1836` (idx 1836..1842, pc 3007..3021) — the copy and the resume;
* `blk1843` (idx 1843..1845, pc 3022..3026) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1831..1835, pc 3000..3006: the `w = 0` test. -/
def blk1831 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1831 .JUMPDEST,
   opAt 1832 (.Dup ⟨1, by decide⟩),
   opAt 1833 .ISZERO,
   pushAt 1834 2 3022,
   opAt 1835 .JUMPI]

/-- Instructions 1836..1842, pc 3007..3021: `ACC := BASE`, then the shift. -/
def blk1836 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1836 2 9344,
   opAt 1837 .MLOAD,
   pushAt 1838 2 2048,
   pushAt 1839 2 1024,
   opAt 1840 .MCOPY,
   pushAt 1841 2 1832,
   opAt 1842 .JUMP]

/-- Instructions 1843..1845, pc 3022..3026: the zero-byte arm. -/
def blk1843 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1843 .JUMPDEST,
   pushAt 1844 2 1789,
   opAt 1845 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
