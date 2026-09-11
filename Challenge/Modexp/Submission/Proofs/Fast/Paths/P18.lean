import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4030) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2557` (idx 2557..2561, pc 4030..3635) — the `w = 0` test;
* `blk2562` (idx 2562..2568, pc 3837..3650) — the copy and the resume;
* `blk2569` (idx 2569..2571, pc 3651..3655) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2557..2561, pc 4030..3635: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2541 .JUMPDEST,
   opAt 2542 (.Dup ⟨1, by decide⟩),
   opAt 2543 .ISZERO,
   pushAt 2544 2 3319,
   opAt 2545 .JUMPI]

/-- Instructions 2562..2568, pc 3837..3650: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2546 2 9344,
   opAt 2547 .MLOAD,
   pushAt 2548 2 2048,
   pushAt 2549 2 1024,
   opAt 2550 .MCOPY,
   pushAt 2551 2 1677,
   opAt 2552 .JUMP]

/-- Instructions 2569..2571, pc 3651..3655: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2553 .JUMPDEST,
   pushAt 2554 2 1634,
   opAt 2555 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2541 ≤ i) (hii : i ≤ 2555) :
    Artifact.submissionArtifact.instructionPC i =
      ([3297,3298,3299,3300,3303,3304,3307,3308,3311,3314,3315,3318,3319,3320,3323] : List Nat)[i - 2541]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3297 = true :=
  Artifact.isValidJumpDest_index 2541 (by rfl)

theorem jumpDest3851 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3319 = true :=
  Artifact.isValidJumpDest_index 2553 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
