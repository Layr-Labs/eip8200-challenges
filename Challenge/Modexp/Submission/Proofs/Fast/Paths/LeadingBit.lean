import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, leading-bit restoration (instructions 2414..2428).

`LZBASE` (pc 3695) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blkLeadingBitTest` (idx 2414..2418, pc 3695..3701) — the `w = 0` test;
* `blkLeadingBitCopy` (idx 2419..2425, pc 3702..3716) — the copy and the resume;
* `blkLeadingBitZero` (idx 2426..2428, pc 3717..3721) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2414..2418, pc 3695..3701: the `w = 0` test. -/
def blkLeadingBitTest :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2414 .JUMPDEST,
   opAt 2415 (.Dup ⟨1, by decide⟩),
   opAt 2416 .ISZERO,
   pushAt 2417 2 3717,
   opAt 2418 .JUMPI]

/-- Instructions 2419..2425, pc 3702..3716: `ACC := BASE`, then the shift. -/
def blkLeadingBitCopy :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2419 2 9344,
   opAt 2420 .MLOAD,
   pushAt 2421 2 2048,
   pushAt 2422 2 1024,
   opAt 2423 .MCOPY,
   pushAt 2424 2 1832,
   opAt 2425 .JUMP]

/-- Instructions 2426..2428, pc 3717..3721: the zero-byte arm. -/
def blkLeadingBitZero :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2426 .JUMPDEST,
   pushAt 2427 2 1789,
   opAt 2428 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
