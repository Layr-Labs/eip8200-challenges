import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 18 (instructions 2557..2571).

`LZBASE` (pc 3865) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2504` (idx 2557..2561, pc 3865..3871) — the `w = 0` test;
* `blk2509` (idx 2562..2568, pc 3872..3886) — the copy and the resume;
* `blk2516` (idx 2569..2571, pc 3887..3891) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2557..2561, pc 3865..3871: the `w = 0` test. -/
def blk2504 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2557 .JUMPDEST,
   opAt 2558 (.Dup ⟨1, by decide⟩),
   opAt 2559 .ISZERO,
   pushAt 2560 2 3887,
   opAt 2561 .JUMPI]

/-- Instructions 2562..2568, pc 3872..3886: `ACC := BASE`, then the shift. -/
def blk2509 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2562 2 9344,
   opAt 2563 .MLOAD,
   pushAt 2564 2 2048,
   pushAt 2565 2 1024,
   opAt 2566 .MCOPY,
   pushAt 2567 2 1832,
   opAt 2568 .JUMP]

/-- Instructions 2569..2571, pc 3887..3891: the zero-byte arm. -/
def blk2516 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2569 .JUMPDEST,
   pushAt 2570 2 1789,
   opAt 2571 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
