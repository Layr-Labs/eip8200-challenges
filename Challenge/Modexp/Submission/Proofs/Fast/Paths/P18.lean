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
  [opAt 2439 .JUMPDEST,
   opAt 2440 (.Dup ⟨1, by decide⟩),
   opAt 2441 .ISZERO,
   pushAt 2442 2 3174,
   opAt 2443 .JUMPI]

/-- Instructions 2562..2568, pc 3872..3650: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2444 2 9344,
   opAt 2445 .MLOAD,
   pushAt 2446 2 2048,
   pushAt 2447 2 1024,
   opAt 2448 .MCOPY,
   pushAt 2449 2 1560,
   opAt 2450 .JUMP]

/-- Instructions 2569..2571, pc 3651..3655: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2451 .JUMPDEST,
   pushAt 2452 2 1519,
   opAt 2453 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2439 ≤ i) (hii : i ≤ 2453) :
    Artifact.submissionArtifact.instructionPC i =
      ([3152,3153,3154,3155,3158,3159,3162,3163,3166,3169,3170,3173,3174,3175,3178] : List Nat)[i - 2439]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3152 = true :=
  Artifact.isValidJumpDest_index 2439 (by rfl)

theorem jumpDest3851 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3174 = true :=
  Artifact.isValidJumpDest_index 2451 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
