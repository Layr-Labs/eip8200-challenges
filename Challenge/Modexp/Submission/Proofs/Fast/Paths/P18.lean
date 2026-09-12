import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4342) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1919.

* `blk2557` (idx 2680..2684, pc 4342..3840) — the `w = 0` test;
* `blk2562` (idx 2685..2691, pc 3872..3840) — the copy and the resume;
* `blk2569` (idx 2692..2694, pc 3840..3840) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2680..2684, pc 4342..3840: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2483 .JUMPDEST,
   opAt 2484 (.Dup ⟨1, by decide⟩),
   opAt 2485 .ISZERO,
   pushAt 2486 2 3256,
   opAt 2487 .JUMPI]

/-- Instructions 2685..2691, pc 3872..3840: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2488 2 5248,
   opAt 2489 .MLOAD,
   pushAt 2490 2 512,
   pushAt 2491 2 256,
   opAt 2492 .MCOPY,
   pushAt 2493 2 1657,
   opAt 2494 .JUMP]

/-- Instructions 2692..2694, pc 3840..3840: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2495 .JUMPDEST,
   pushAt 2496 2 1616,
   opAt 2497 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2483 ≤ i) (hii : i ≤ 2497) :
    Artifact.submissionArtifact.instructionPC i =
      ([3234,3235,3236,3237,3240,3241,3244,3245,3248,3251,3252,3255,3256,3257,3260] : List Nat)[i - 2483]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3234 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

theorem jumpDest3851 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3256 = true :=
  Artifact.isValidJumpDest_index 2495 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
