import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4260) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1837.

* `blk2557` (idx 2598..2602, pc 4260..3840) — the `w = 0` test;
* `blk2562` (idx 2603..2609, pc 3872..3840) — the copy and the resume;
* `blk2569` (idx 2610..2612, pc 3840..3840) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2598..2602, pc 4260..3840: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2445 .JUMPDEST,
   opAt 2446 (.Dup ⟨1, by decide⟩),
   opAt 2447 .ISZERO,
   pushAt 2448 2 3174,
   opAt 2449 .JUMPI]

/-- Instructions 2603..2609, pc 3872..3840: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2450 2 9344,
   opAt 2451 .MLOAD,
   pushAt 2452 2 2048,
   pushAt 2453 2 1024,
   opAt 2454 .MCOPY,
   pushAt 2455 2 1575,
   opAt 2456 .JUMP]

/-- Instructions 2610..2612, pc 3840..3840: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2457 .JUMPDEST,
   pushAt 2458 2 1534,
   opAt 2459 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2445 ≤ i) (hii : i ≤ 2459) :
    Artifact.submissionArtifact.instructionPC i =
      ([3152,3153,3154,3155,3158,3159,3162,3163,3166,3169,3170,3173,3174,3175,3178] : List Nat)[i - 2445]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3152 = true :=
  Artifact.isValidJumpDest_index 2445 (by rfl)

theorem jumpDest3851 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3174 = true :=
  Artifact.isValidJumpDest_index 2457 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
