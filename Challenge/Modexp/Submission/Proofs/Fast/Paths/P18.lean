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
  [opAt 2635 .JUMPDEST,
   opAt 2636 (.Dup ⟨1, by decide⟩),
   opAt 2637 .ISZERO,
   pushAt 2638 2 3646,
   opAt 2639 .JUMPI]

/-- Instructions 2562..2568, pc 3872..3650: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2640 2 9344,
   opAt 2641 .MLOAD,
   pushAt 2642 2 2048,
   pushAt 2643 2 1024,
   opAt 2644 .MCOPY,
   pushAt 2645 2 1832,
   opAt 2646 .JUMP]

/-- Instructions 2569..2571, pc 3651..3655: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2647 .JUMPDEST,
   pushAt 2648 2 1789,
   opAt 2649 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2635 ≤ i) (hii : i ≤ 2649) :
    Artifact.submissionArtifact.instructionPC i =
      ([3624,3625,3626,3627,3630,3631,3634,3635,3638,3641,3642,3645,3646,3647,3650] : List Nat)[i - 2635]! := by
  interval_cases i <;> decide

theorem jumpDest3865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3624 = true :=
  Artifact.isValidJumpDest_index 2635 (by rfl)

theorem jumpDest3887 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3646 = true :=
  Artifact.isValidJumpDest_index 2647 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
