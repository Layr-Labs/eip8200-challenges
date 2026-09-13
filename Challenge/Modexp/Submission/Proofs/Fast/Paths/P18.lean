import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4345) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1827.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1914.

* `blk2557` (idx 2690..2694, pc 4345..3840) — the `w = 0` test;
* `blk2562` (idx 2695..2701, pc 3872..3840) — the copy and the resume;
* `blk2569` (idx 2702..2704, pc 3840..3840) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2690..2694, pc 4345..3840: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2469 .JUMPDEST,
   opAt 2470 (.Dup ⟨1, by decide⟩),
   opAt 2471 .ISZERO,
   pushAt 2472 2 1611,
   opAt 2473 .JUMPI]

/-- Instructions 2695..2701, pc 3872..3840: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2474 2 2688,
   opAt 2475 .MLOAD,
   pushAt 2476 2 512,
   pushAt 2477 2 256,
   opAt 2478 .MCOPY,
   pushAt 2479 2 1652,
   opAt 2480 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 2469 ≤ i) (hii : i ≤ 2481) :
    Artifact.submissionArtifact.instructionPC i =
      ([3243,3244,3245,3246,3249,3250,3253,3254,3257,3260,3261,3264,3265] : List Nat)[i - 2469]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3243 = true :=
  Artifact.isValidJumpDest_index 2469 (by rfl)


end Challenge.Modexp.Submission.Proofs.Fast
