import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4080) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2557` (idx 2553..2557, pc 4080..3657) — the `w = 0` test;
* `blk2562` (idx 2558..2564, pc 3872..3657) — the copy and the resume;
* `blk2569` (idx 2565..2567, pc 3657..3657) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2553..2557, pc 4080..3657: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2413 .JUMPDEST,
   opAt 2414 (.Dup ⟨1, by decide⟩),
   opAt 2415 .ISZERO,
   pushAt 2416 2 3129,
   opAt 2417 .JUMPI]

/-- Instructions 2558..2564, pc 3872..3657: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2418 2 9344,
   opAt 2419 .MLOAD,
   pushAt 2420 2 2048,
   pushAt 2421 2 1024,
   opAt 2422 .MCOPY,
   pushAt 2423 2 1527,
   opAt 2424 .JUMP]

/-- Instructions 2565..2567, pc 3657..3657: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2425 .JUMPDEST,
   pushAt 2426 2 1486,
   opAt 2427 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2413 ≤ i) (hii : i ≤ 2427) :
    Artifact.submissionArtifact.instructionPC i =
      ([3107,3108,3109,3110,3113,3114,3117,3118,3121,3124,3125,3128,3129,3130,3133] : List Nat)[i - 2413]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3107 = true :=
  Artifact.isValidJumpDest_index 2413 (by rfl)

theorem jumpDest3851 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3129 = true :=
  Artifact.isValidJumpDest_index 2425 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
