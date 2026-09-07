import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 18 (instructions 2588..2602).

`LZBASE` (pc 3909) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2504` (idx 2588..2592, pc 3909..3915) — the `w = 0` test;
* `blk2509` (idx 2593..2599, pc 3916..3930) — the copy and the resume;
* `blk2516` (idx 2600..2602, pc 3931..3935) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem lzBasePC (i : Nat) (hi : 2588 ≤ i) (hii : i ≤ 2602) :
    Artifact.submissionArtifact.instructionPC i =
      [3909,3910,3911,3912,3915,3916,3919,3920,3923,3926,3927,3930,3931,
       3932,3935][i - 2588]! := by
  interval_cases i <;> decide

/-- Instructions 2588..2592, pc 3909..3915: the `w = 0` test. -/
def blk2504 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2588 .JUMPDEST,
   opAt 2589 (.Dup ⟨1, by decide⟩),
   opAt 2590 .ISZERO,
   pushAt 2591 2 3931,
   opAt 2592 .JUMPI]

/-- Instructions 2593..2599, pc 3916..3930: `ACC := BASE`, then the shift. -/
def blk2509 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2593 2 9344,
   opAt 2594 .MLOAD,
   pushAt 2595 2 2048,
   pushAt 2596 2 1024,
   opAt 2597 .MCOPY,
   pushAt 2598 2 1832,
   opAt 2599 .JUMP]

/-- Instructions 2600..2602, pc 3931..3935: the zero-byte arm. -/
def blk2516 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2600 .JUMPDEST,
   pushAt 2601 2 1789,
   opAt 2602 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
