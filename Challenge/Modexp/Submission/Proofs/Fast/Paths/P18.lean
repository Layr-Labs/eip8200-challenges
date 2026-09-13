import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4347) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1829.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1916.

* `blk2557` (idx 2692..2696, pc 4347..3840) — the `w = 0` test;
* `blk2562` (idx 2697..2703, pc 3872..3840) — the copy and the resume;
* `blk2569` (idx 2704..2706, pc 3840..3840) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2692..2696, pc 4347..3840: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2425 .JUMPDEST,
   opAt 2426 (.Dup ⟨1, by decide⟩),
   opAt 2427 .ISZERO,
   pushAt 2428 2 1611,
   opAt 2429 .JUMPI]

/-- Instructions 2697..2703, pc 3872..3840: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2430 2 2688,
   opAt 2431 .MLOAD,
   pushAt 2432 2 512,
   pushAt 2433 2 256,
   opAt 2434 .MCOPY,
   pushAt 2435 2 1652,
   opAt 2436 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2425 ≤ i) (hii : i ≤ 2437) :
    Artifact.submissionArtifact.instructionPC i =
      ([3194,3195,3196,3197,3200,3201,3204,3205,3208,3211,3212,3215,3216] : List Nat)[i - 2425]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3194 = true :=
  Artifact.isValidJumpDest_index 2425 (by rfl)


end Challenge.Modexp.Submission.Proofs.Fast
