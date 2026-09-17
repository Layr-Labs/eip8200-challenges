import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandL1
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

/-!
# The seven uniform first-loop blocks of the sqCP1m kernel (located)

Block `k = 1..7` is instruction `3190 + 32(k-1)`, 32 instructions, pc `4296 + 37(k-1)`,
program `StagedOperand.stepProgram (32(7-k)) (2112 + 32(7-k))`.  Split from `KernelChain`
so that the (slow) located-block certificates are elaborated once.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.KernelChain

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached StagedOperand

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

def l1Block1 : Block Artifact.submissionArtifact .Osaka 3490 (stepProgram 192 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2810 31 3490 (stepProgram 192 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block2 : Block Artifact.submissionArtifact .Osaka 3527 (stepProgram 160 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2841 31 3527 (stepProgram 160 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block3 : Block Artifact.submissionArtifact .Osaka 3564 (stepProgram 128 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2872 31 3564 (stepProgram 128 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block4 : Block Artifact.submissionArtifact .Osaka 3601 (stepProgram 96 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2903 31 3601 (stepProgram 96 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block5 : Block Artifact.submissionArtifact .Osaka 3638 (stepProgram 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2934 31 3638 (stepProgram 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block6 : Block Artifact.submissionArtifact .Osaka 3675 (stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2965 31 3675 (stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block7 : Block Artifact.submissionArtifact .Osaka 3712 (stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2996 31 3712 (stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

/-! ## The private four-limb ladder copy (5172-5313)

The four-limb multiply rows no longer share the ladder at 3528: the setup computes
`ent = 5172`, the entry of a byte copy of 3528-3665 that keeps its own tail jump.  Because
the copy is byte-identical, blocks k5..k7 reuse the very same `stepProgram` literals -- only
the instruction indices and program counters differ. -/

def l1Block5Copy : Block Artifact.submissionArtifact .Osaka 5282 (stepProgram 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4263 31 5282 (stepProgram 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block6Copy : Block Artifact.submissionArtifact .Osaka 5319 (stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4294 31 5319 (stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block7Copy : Block Artifact.submissionArtifact .Osaka 5356 (stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4325 31 5356 (stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest5172 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5282 = true :=
  Artifact.isValidJumpDest_index 4263 (by rfl)
theorem jumpDest5209 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5319 = true :=
  Artifact.isValidJumpDest_index 4294 (by rfl)
theorem jumpDest5246 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5356 = true :=
  Artifact.isValidJumpDest_index 4325 (by rfl)

/-! ## Jump destinations of the chain entries (block `k` for `k = 1..7`, and the
middle `JUMPDEST` = entry `k = 8`) -/

theorem jumpDest4068 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3490 = true :=
  Artifact.isValidJumpDest_index 2810 (by rfl)
theorem jumpDest4106 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3527 = true :=
  Artifact.isValidJumpDest_index 2841 (by rfl)
theorem jumpDest4144 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3564 = true :=
  Artifact.isValidJumpDest_index 2872 (by rfl)
theorem jumpDest4182 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3601 = true :=
  Artifact.isValidJumpDest_index 2903 (by rfl)
theorem jumpDest4220 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3638 = true :=
  Artifact.isValidJumpDest_index 2934 (by rfl)
theorem jumpDest4258 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3675 = true :=
  Artifact.isValidJumpDest_index 2965 (by rfl)
theorem jumpDest4296 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3712 = true :=
  Artifact.isValidJumpDest_index 2996 (by rfl)
theorem jumpDest4334 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3749 = true :=
  Artifact.isValidJumpDest_index 3027 (by rfl)

/-- Every chain entry `3494 + 37(k-1)`, `1 ≤ k ≤ 8`, is a valid jump destination.
Base transcribed: the eight cited theorems prove pcs 3494 3531 3568 3605 3642 3679
3716 3753, all confirmed JUMPDESTs in `fe8e9f61e6d3764a`; 3494 is also `l1Target 8`. -/
theorem jumpDest_l1Entry (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (3494 + 37 * (k - 1)) = true := by
  match k, hk1, hk8 with
  | 1, _, _ => exact jumpDest4068
  | 2, _, _ => exact jumpDest4106
  | 3, _, _ => exact jumpDest4144
  | 4, _, _ => exact jumpDest4182
  | 5, _, _ => exact jumpDest4220
  | 6, _, _ => exact jumpDest4258
  | 7, _, _ => exact jumpDest4296
  | 8, _, _ => exact jumpDest4334
  | 0, h, _ => exact absurd h (by decide)
  | k + 9, _, h => exact absurd h (by omega)

/-- The copy's middle-block entry, pc 5397 (= `5138 + 37*7`). -/
theorem jumpDest5283 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5393 = true :=
  Artifact.isValidJumpDest_index 4356 (by rfl)

/-- Every chain entry of the private four-limb ladder copy, `5138 + 37(k-1)` for
`5 ≤ k ≤ 8`, is a valid jump destination -- the mirror of `jumpDest_l1Entry`. -/
theorem jumpDest_l1EntryCopy (k : Nat) (hk5 : 5 ≤ k) (hk8 : k ≤ 8) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (5134 + 37 * (k - 1)) = true := by
  match k, hk5, hk8 with
  | 5, _, _ => exact jumpDest5172
  | 6, _, _ => exact jumpDest5209
  | 7, _, _ => exact jumpDest5246
  | 8, _, _ => exact jumpDest5283
  | 0, h, _ => exact absurd h (by decide)
  | 1, h, _ => exact absurd h (by decide)
  | 2, h, _ => exact absurd h (by decide)
  | 3, h, _ => exact absurd h (by decide)
  | 4, h, _ => exact absurd h (by decide)
  | k + 9, _, h => exact absurd h (by omega)

end Challenge.Modexp.Submission.Proofs.Fast.KernelChain
