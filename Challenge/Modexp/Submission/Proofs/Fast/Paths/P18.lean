import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 18 (instructions 2557..2571).

`LZBASE` (pc 3858) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2504` (idx 2552..2556, pc 3858..3864) — the `w = 0` test;
* `blk2509` (idx 2557..2563, pc 3865..3879) — the copy and the resume;
* `blk2516` (idx 2564..2566, pc 3880..3884) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem lzBasePC (i : Nat) (hi : 2552 ≤ i) (hii : i ≤ 2566) :
    Artifact.submissionArtifact.instructionPC i =
      [3858,3859,3860,3861,3864,3865,3868,3869,3872,3875,3876,3879,3880,
       3881,3884][i - 2552]! := by
  interval_cases i <;> decide

/-- Instructions 2552..2556, pc 3858..3864: the `w = 0` test. -/
def blk2504 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2552 .JUMPDEST,
   opAt 2553 (.Dup ⟨1, by decide⟩),
   opAt 2554 .ISZERO,
   pushAt 2555 2 3880,
   opAt 2556 .JUMPI]

/-- Instructions 2557..2563, pc 3865..3879: `ACC := BASE`, then the shift. -/
def blk2509 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2557 2 9344,
   opAt 2558 .MLOAD,
   pushAt 2559 2 2048,
   pushAt 2560 2 1024,
   opAt 2561 .MCOPY,
   pushAt 2562 2 1832,
   opAt 2563 .JUMP]

/-- Instructions 2564..2566, pc 3880..3884: the zero-byte arm. -/
def blk2516 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2564 .JUMPDEST,
   pushAt 2565 2 1789,
   opAt 2566 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
