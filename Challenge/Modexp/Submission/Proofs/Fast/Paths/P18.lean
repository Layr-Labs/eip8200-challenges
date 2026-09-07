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

* `blk2557` (idx 2557..2561, pc 3865..3871) — the `w = 0` test;
* `blk2562` (idx 2562..2568, pc 3872..3886) — the copy and the resume;
* `blk2569` (idx 2569..2571, pc 3887..3891) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2557..2561, pc 3865..3871: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2475 .JUMPDEST,
   opAt 2476 (.Dup ⟨1, by decide⟩),
   opAt 2477 .ISZERO,
   pushAt 2478 2 3887,
   opAt 2479 .JUMPI]

/-- Instructions 2562..2568, pc 3872..3886: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2480 2 9344,
   opAt 2481 .MLOAD,
   pushAt 2482 2 2048,
   pushAt 2483 2 1024,
   opAt 2484 .MCOPY,
   pushAt 2485 2 1832,
   opAt 2486 .JUMP]

/-- Instructions 2569..2571, pc 3887..3891: the zero-byte arm. -/
def blk2569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2487 .JUMPDEST,
   pushAt 2488 2 1789,
   opAt 2489 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2475 ≤ i) (hii : i ≤ 2489) :
    Artifact.submissionArtifact.instructionPC i =
      ([3865,3866,3867,3868,3871,3872,3875,3876,3879,3882,3883,3886,3887,3888,3891] : List Nat)[i - 2475]! := by
  interval_cases i <;> decide

theorem jumpDest3865 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3865 = true :=
  Artifact.isValidJumpDest_index 2475 (by rfl)

theorem jumpDest3887 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3887 = true :=
  Artifact.isValidJumpDest_index 2487 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
