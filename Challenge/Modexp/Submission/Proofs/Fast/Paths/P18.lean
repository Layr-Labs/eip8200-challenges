import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 18 (instructions 2582..2596).

`LZBASE` (pc 3894) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2504` (idx 2582..2586, pc 3894..3900) — the `w = 0` test;
* `blk2509` (idx 2587..2593, pc 3901..3915) — the copy and the resume;
* `blk2516` (idx 2594..2596, pc 3916..3920) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem lzBasePC (i : Nat) (hi : 2582 ≤ i) (hii : i ≤ 2596) :
    Artifact.submissionArtifact.instructionPC i =
      [3894,3895,3896,3897,3900,3901,3904,3905,3908,3911,3912,3915,3916,
       3917,3920][i - 2582]! := by
  interval_cases i <;> decide

/-- Instructions 2582..2586, pc 3894..3900: the `w = 0` test. -/
def blk2504 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   opAt 2583 (.Dup ⟨1, by decide⟩),
   opAt 2584 .ISZERO,
   pushAt 2585 2 3916,
   opAt 2586 .JUMPI]

/-- Instructions 2587..2593, pc 3901..3915: `ACC := BASE`, then the shift. -/
def blk2509 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2587 2 9344,
   opAt 2588 .MLOAD,
   pushAt 2589 2 2048,
   pushAt 2590 2 1024,
   opAt 2591 .MCOPY,
   pushAt 2592 2 1832,
   opAt 2593 .JUMP]

/-- Instructions 2594..2596, pc 3916..3920: the zero-byte arm. -/
def blk2516 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2594 .JUMPDEST,
   pushAt 2595 2 1789,
   opAt 2596 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
