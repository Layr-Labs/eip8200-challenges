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

* `blk2557` (idx 2485..2489, pc 3865..3871) — the `w = 0` test;
* `blk2562` (idx 2490..2496, pc 3872..3886) — the copy and the resume;
* `blk2569` (idx 2497..2499, pc 3887..3891) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2485..2489, pc 3865..3871: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2485 .JUMPDEST,
   opAt 2486 (.Dup ⟨1, by decide⟩),
   opAt 2487 .ISZERO,
   pushAt 2488 2 3887,
   opAt 2489 .JUMPI]

/-- Instructions 2490..2496, pc 3872..3886: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2490 2 9344,
   opAt 2491 .MLOAD,
   pushAt 2492 2 2048,
   pushAt 2493 2 1024,
   opAt 2494 .MCOPY,
   pushAt 2495 2 1832,
   opAt 2496 .JUMP]

/-- Instructions 2497..2499, pc 3887..3891: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2497 .JUMPDEST,
   pushAt 2498 2 1789,
   opAt 2499 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat) (hi : 2485 ≤ i) (hii : i ≤ 2499) :
    Artifact.submissionArtifact.instructionPC i =
      [3865, 3866, 3867, 3868, 3871,
       3872, 3875, 3876, 3879, 3882, 3883, 3886,
       3887, 3888, 3891][i - 2485]! := by
  interval_cases i <;> decide

theorem jumpDest3865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3865 = true :=
  Artifact.isValidJumpDest_index 2485 (by rfl)

theorem jumpDest3887 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3887 = true :=
  Artifact.isValidJumpDest_index 2497 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
