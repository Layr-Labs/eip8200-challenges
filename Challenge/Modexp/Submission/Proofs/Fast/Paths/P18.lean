import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 18 (instructions 2574..2588).

`LZBASE` (pc 3896) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2574` (idx 2574..2578, pc 3896..3902) — the `w = 0` test;
* `blk2579` (idx 2579..2585, pc 3903..3917) — the copy and the resume;
* `blk2586` (idx 2586..2588, pc 3918..3922) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2574..2578, pc 3896..3902: the `w = 0` test. -/
def blk2574 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2574 .JUMPDEST,
   opAt 2575 (.Dup ⟨1, by decide⟩),
   opAt 2576 .ISZERO,
   pushAt 2577 2 3918,
   opAt 2578 .JUMPI]

/-- Instructions 2579..2585, pc 3903..3917: `ACC := BASE`, then the shift. -/
def blk2579 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2579 2 9344,
   opAt 2580 .MLOAD,
   pushAt 2581 2 2048,
   pushAt 2582 2 1024,
   opAt 2583 .MCOPY,
   pushAt 2584 2 1832,
   opAt 2585 .JUMP]

/-- Instructions 2586..2588, pc 3918..3922: the zero-byte arm. -/
def blk2586 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2586 .JUMPDEST,
   pushAt 2587 2 1789,
   opAt 2588 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
