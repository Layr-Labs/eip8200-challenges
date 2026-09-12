import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4121) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2557` (idx 2557..2561, pc 4121..3635) — the `w = 0` test;
* `blk2562` (idx 2562..2568, pc 3872..3650) — the copy and the resume;
* `blk2569` (idx 2569..2571, pc 3651..3655) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2557..2561, pc 4121..3635: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2468 .JUMPDEST,
   opAt 2469 (.Dup ⟨1, by decide⟩),
   opAt 2470 .ISZERO,
   pushAt 2471 2 3268,
   opAt 2472 .JUMPI]

/-- Instructions 2562..2568, pc 3872..3650: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2473 2 5248,
   opAt 2474 .MLOAD,
   pushAt 2475 2 512,
   pushAt 2476 2 256,
   opAt 2477 .MCOPY,
   pushAt 2478 2 1662,
   opAt 2479 .JUMP]

/-- Instructions 2569..2571, pc 3651..3655: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2480 .JUMPDEST,
   pushAt 2481 2 1621,
   opAt 2482 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2468 ≤ i) (hii : i ≤ 2482) :
    Artifact.submissionArtifact.instructionPC i =
      ([3246,3247,3248,3249,3252,3253,3256,3257,3260,3263,3264,3267,3268,3269,3272] : List Nat)[i - 2468]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3246 = true :=
  Artifact.isValidJumpDest_index 2468 (by rfl)

theorem jumpDest3851 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3268 = true :=
  Artifact.isValidJumpDest_index 2480 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
