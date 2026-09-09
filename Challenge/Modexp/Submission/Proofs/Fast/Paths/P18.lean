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
  [opAt 2651 .JUMPDEST,
   opAt 2652 (.Dup ⟨1, by decide⟩),
   opAt 2653 .ISZERO,
   pushAt 2654 2 3639,
   opAt 2655 .JUMPI]

/-- Instructions 2562..2568, pc 3872..3650: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2656 2 9344,
   opAt 2657 .MLOAD,
   pushAt 2658 2 2048,
   pushAt 2659 2 1024,
   opAt 2660 .MCOPY,
   pushAt 2661 2 1823,
   opAt 2662 .JUMP]

/-- Instructions 2569..2571, pc 3651..3655: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2663 .JUMPDEST,
   pushAt 2664 2 1780,
   opAt 2665 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2651 ≤ i) (hii : i ≤ 2665) :
    Artifact.submissionArtifact.instructionPC i =
      ([3617,3618,3619,3620,3623,3624,3627,3628,3631,3634,3635,3638,3639,3640,3643] : List Nat)[i - 2651]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3617 = true :=
  Artifact.isValidJumpDest_index 2651 (by rfl)

theorem jumpDest3851 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3639 = true :=
  Artifact.isValidJumpDest_index 2663 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
