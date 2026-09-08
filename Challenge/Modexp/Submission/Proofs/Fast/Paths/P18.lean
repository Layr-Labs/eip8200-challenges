import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 3865) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2557` (idx 2557..2561, pc 3865..3379) — the `w = 0` test;
* `blk2562` (idx 2562..2568, pc 3872..3394) — the copy and the resume;
* `blk2569` (idx 2569..2571, pc 3395..3399) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2557..2561, pc 3865..3379: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2398 .JUMPDEST,
   opAt 2399 (.Dup ⟨1, by decide⟩),
   opAt 2400 .ISZERO,
   pushAt 2401 2 3369,
   opAt 2402 .JUMPI]

/-- Instructions 2562..2568, pc 3872..3394: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2403 2 9344,
   opAt 2404 .MLOAD,
   pushAt 2405 2 2048,
   pushAt 2406 2 1024,
   opAt 2407 .MCOPY,
   pushAt 2408 2 1823,
   opAt 2409 .JUMP]

/-- Instructions 2569..2571, pc 3395..3399: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2410 .JUMPDEST,
   pushAt 2411 2 1780,
   opAt 2412 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2398 ≤ i) (hii : i ≤ 2412) :
    Artifact.submissionArtifact.instructionPC i =
      [3347,3348,3349,3350,3353,3354,3357,3358,3361,3364,3365,3368,3369,3370,3373][i - 2398]! := by
  interval_cases i <;> decide

theorem jumpDest3865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3347 = true :=
  Artifact.isValidJumpDest_index 2398 (by rfl)

theorem jumpDest3887 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3369 = true :=
  Artifact.isValidJumpDest_index 2410 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
