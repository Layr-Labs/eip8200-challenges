import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the relocated leading-bit shortcut.

`LZBASE` (pc 4337) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1828.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1916.

* `blk2557` (idx 2692..2696, pc 4342..3840) — the `w = 0` test;
* `blk2562` (idx 2697..2703, pc 3872..3840) — the copy and the resume;
* `blk2569` (idx 2704..2701, pc 3840..3840) — the zero-byte arm. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2692..2696, pc 4342..3840: the `w = 0` test. -/
def blk2557 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1966 .JUMPDEST,
   opAt 1967 (.Dup ⟨1, by decide⟩),
   opAt 1968 .ISZERO,
   pushAt 1969 2 1060,
   opAt 1970 .JUMPI]

/-- Instructions 2697..2703, pc 3872..3840: `ACC := BASE`, then the shift. -/
def blk2562 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1971 2 2688,
   opAt 1972 .MLOAD,
   pushAt 1973 2 512,
   pushAt 1974 2 256,
   opAt 1975 .MCOPY,
   pushAt 1976 2 1101,
   opAt 1977 .JUMP]

/-- PC table for the relocated leading-bit shortcut.  This range is outside
the inherited `Fast.Defs` tables, so execution proofs need a local certificate
instead of unfolding the complete bytecode prefix at every instruction. -/
@[simp] theorem leadingBitPC (i : Nat)
    (hi : 1966 ≤ i) (hii : i ≤ 1978) :
    Artifact.submissionArtifact.instructionPC i =
      ([2609,2610,2611,2612,2615,2616,2619,2620,2623,2626,2627,2630,2631] : List Nat)[i - 1966]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3829 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2609 = true :=
  Artifact.isValidJumpDest_index 1966 (by rfl)


end Challenge.Modexp.Submission.Proofs.Fast
