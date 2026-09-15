import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4342) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
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
  [opAt 1833 .JUMPDEST,
   opAt 1834 (.Dup ⟨1, by decide⟩),
   opAt 1835 .ISZERO,
   pushAt 1836 2 951,
   opAt 1837 .JUMPI]

/-- Instructions 2697..2703, pc 3872..3840: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1838 2 2688,
   opAt 1839 .MLOAD,
   pushAt 1840 2 512,
   pushAt 1841 2 256,
   opAt 1842 .MCOPY,
   pushAt 1843 2 992,
   opAt 1844 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 1833 ≤ i) (hii : i ≤ 1845) :
    Artifact.submissionArtifact.instructionPC i =
      ([2421,2422,2423,2424,2427,2428,2431,2432,2435,2438,2439,2442,2443] : List Nat)[i - 1833]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2421 = true :=
  Artifact.isValidJumpDest_index 1833 (by rfl)


end Challenge.Modexp.Submission.Proofs.Fast
