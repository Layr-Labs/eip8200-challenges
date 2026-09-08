import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 3865) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

* `blk2557` (idx 2557..2561, pc 3865..3379) — the `w = 0` test;
* `blk2562` (idx 2562..2568, pc 3872..3394) — the copy and the resume;
* `blk2569` (idx 2569..2571, pc 3395..3399) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2557..2561, pc 3865..3379: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2419 .JUMPDEST,
   opAt 2420 (.Dup ⟨1, by decide⟩),
   opAt 2421 .ISZERO,
   pushAt 2422 2 3390,
   opAt 2423 .JUMPI]

/-- Instructions 2562..2568, pc 3872..3394: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2424 2 9344,
   opAt 2425 .MLOAD,
   pushAt 2426 2 2048,
   pushAt 2427 2 1024,
   opAt 2428 .MCOPY,
   pushAt 2429 2 1832,
   opAt 2430 .JUMP]

/-- Instructions 2569..2571, pc 3395..3399: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2431 .JUMPDEST,
   pushAt 2432 2 1789,
   opAt 2433 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2419 ≤ i) (hii : i ≤ 2433) :
    Artifact.submissionArtifact.instructionPC i =
      ([3368,3369,3370,3371,3374,3375,3378,3379,3382,3385,3386,3389,3390,3391,3394] : List Nat)[i - 2419]! := by
  interval_cases i <;> decide

theorem jumpDest3865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3368 = true :=
  Artifact.isValidJumpDest_index 2419 (by rfl)

theorem jumpDest3887 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3390 = true :=
  Artifact.isValidJumpDest_index 2431 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
