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
  [opAt 1983 .JUMPDEST,
   opAt 1984 (.Dup ⟨1, by decide⟩),
   opAt 1985 .ISZERO,
   pushAt 1986 2 1077,
   opAt 1987 .JUMPI]

/-- Instructions 2697..2703, pc 3872..3840: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1988 2 2688,
   opAt 1989 .MLOAD,
   pushAt 1990 2 512,
   pushAt 1991 2 256,
   opAt 1992 .MCOPY,
   pushAt 1993 2 1118,
   opAt 1994 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 1983 ≤ i) (hii : i ≤ 1995) :
    Artifact.submissionArtifact.instructionPC i =
      ([2660,2661,2662,2663,2666,2667,2670,2671,2674,2677,2678,2681,2682] : List Nat)[i - 1983]! := by
  interval_cases i <;> decide

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2660 = true :=
  Artifact.isValidJumpDest_index 1983 (by rfl)


end Challenge.Modexp.Submission.Proofs.Fast
