import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 18 (instructions 2557..2570).

`LZBASE` (pc 3865) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2504` (idx 2557..2561, pc 3865..3871) — the `w = 0` test;
* `blk2509` (idx 2562..2567, pc 3872..3883) — the stack-cached copy and resume;
* `blk2516` (idx 2568..2570, pc 3884..3888) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem lzBasePC (i : Nat) (hi : 2557 ≤ i) (hii : i ≤ 2570) :
    Artifact.submissionArtifact.instructionPC i =
      [3865,3866,3867,3868,3871,3872,3873,3876,3879,3880,3883,3884,3885,3888][i - 2557]! := by
  interval_cases i <;> decide

/- Instructions 2557..2561, pc 3865..3871: the `w = 0` test. -/
def blk2504 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2557 .JUMPDEST,
   opAt 2558 (.Dup ⟨1, by decide⟩),
   opAt 2559 .ISZERO,
   pushAt 2560 2 3884,
   opAt 2561 .JUMPI]

/- Instructions 2562..2567, pc 3872..3883: `ACC := BASE`, then the stack-cached resume. -/
def blk2509 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2562 (.Dup ⟨3, by decide⟩),
   pushAt 2563 2 2048,
   pushAt 2564 2 1024,
   opAt 2565 .MCOPY,
   pushAt 2566 2 1832,
   opAt 2567 .JUMP]

/- Instructions 2568..2570, pc 3884..3888: the zero-byte arm. -/
def blk2516 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2568 .JUMPDEST,
   pushAt 2569 2 1789,
   opAt 2570 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
