import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4370) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1829.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1916.

* `blk2557` (idx 2692..2696, pc 4347..3840) — the `w = 0` test;
* `blk2562` (idx 2697..2703, pc 3868..3840) — the copy and the resume;
* `blk2569` (idx 2704..2706, pc 3840..3840) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2692..2696, pc 4347..3840: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1623 .JUMPDEST,
   opAt 1624 (.Dup ⟨1, by decide⟩),
   opAt 1625 .ISZERO,
   pushAt 1626 2 962,
   opAt 1627 .JUMPI]

/-- Instructions 2697..2703, pc 3868..3840: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1628 2 2688,
   opAt 1629 .MLOAD,
   pushAt 1630 2 512,
   pushAt 1631 2 256,
   opAt 1632 .MCOPY,
   pushAt 1633 2 1003,
   opAt 1634 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 1623 ≤ i) (hii : i ≤ 1635) :
    Artifact.submissionArtifact.instructionPC i =
      ([2160,2161,2162,2163,2166,2167,2170,2171,2174,2177,2178,2181,2182] : List Nat)[i - 1623]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2160 = true :=
  Artifact.isValidJumpDest_index 1623 (by rfl)


end Challenge.Modexp.Submission.Proofs.Fast
