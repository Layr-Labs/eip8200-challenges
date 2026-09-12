import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4355) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1919.

* `blk2557` (idx 2695..2699, pc 4355..3840) — the `w = 0` test;
* `blk2562` (idx 2700..2706, pc 3872..3840) — the copy and the resume;
* `blk2569` (idx 2707..2709, pc 3840..3840) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2695..2699, pc 4355..3840: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2472 .JUMPDEST,
   opAt 2473 (.Dup ⟨1, by decide⟩),
   opAt 2474 .ISZERO,
   pushAt 2475 2 1616,
   opAt 2476 .JUMPI]

/-- Instructions 2700..2706, pc 3872..3840: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2477 2 5248,
   opAt 2478 .MLOAD,
   pushAt 2479 2 512,
   pushAt 2480 2 256,
   opAt 2481 .MCOPY,
   pushAt 2482 2 1657,
   opAt 2483 .JUMP]

/-- Instructions 2707..2709, pc 3840..3840: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2484 .JUMPDEST,
   pushAt 2485 2 1616,
   opAt 2486 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2472 ≤ i) (hii : i ≤ 2486) :
    Artifact.submissionArtifact.instructionPC i =
      ([3248,3249,3250,3251,3254,3255,3258,3259,3262,3265,3266,3269,3270,3271,3274] : List Nat)[i - 2472]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3248 = true :=
  Artifact.isValidJumpDest_index 2472 (by rfl)

theorem jumpDest3851 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3270 = true :=
  Artifact.isValidJumpDest_index 2484 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
