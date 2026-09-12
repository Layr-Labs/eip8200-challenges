import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandL1
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

/-!
# The seven uniform first-loop blocks of the sqCP1m kernel (located)

Block `k = 1..7` is instruction `3071 + 32(k-1)`, 32 instructions, pc `4068 + 38(k-1)`,
program `StagedOperand.stepProgram (32(7-k)) (4160 + 32(7-k))`.  Split from `KernelChain`
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

def l1Block1 : Block Artifact.submissionArtifact .Osaka 4215 (stepProgram 192 4352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3165 31 4215 (stepProgram 192 4352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block2 : Block Artifact.submissionArtifact .Osaka 4253 (stepProgram 160 4320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3196 31 4253 (stepProgram 160 4320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block3 : Block Artifact.submissionArtifact .Osaka 4291 (stepProgram 128 4288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3227 31 4291 (stepProgram 128 4288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block4 : Block Artifact.submissionArtifact .Osaka 4329 (stepProgram 96 4256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3258 31 4329 (stepProgram 96 4256)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block5 : Block Artifact.submissionArtifact .Osaka 4367 (stepProgram 64 4224) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3289 31 4367 (stepProgram 64 4224)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block6 : Block Artifact.submissionArtifact .Osaka 4405 (stepProgram 32 4192) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3320 31 4405 (stepProgram 32 4192)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block7 : Block Artifact.submissionArtifact .Osaka 4443 (stepProgram 0 4160) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3351 31 4443 (stepProgram 0 4160)
    (by decide) (by rfl) (by rfl) (by decide)

/-! ## Jump destinations of the chain entries (block `k` for `k = 1..7`, and the
middle `JUMPDEST` = entry `k = 8`) -/

theorem jumpDest4068 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4215 = true :=
  Artifact.isValidJumpDest_index 3165 (by rfl)
theorem jumpDest4106 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4253 = true :=
  Artifact.isValidJumpDest_index 3196 (by rfl)
theorem jumpDest4144 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4291 = true :=
  Artifact.isValidJumpDest_index 3227 (by rfl)
theorem jumpDest4182 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4329 = true :=
  Artifact.isValidJumpDest_index 3258 (by rfl)
theorem jumpDest4220 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4367 = true :=
  Artifact.isValidJumpDest_index 3289 (by rfl)
theorem jumpDest4258 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4405 = true :=
  Artifact.isValidJumpDest_index 3320 (by rfl)
theorem jumpDest4296 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4443 = true :=
  Artifact.isValidJumpDest_index 3351 (by rfl)
theorem jumpDest4334 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4481 = true :=
  Artifact.isValidJumpDest_index 3382 (by rfl)

/-- Every chain entry `4068 + 38(k-1)`, `1 ≤ k ≤ 8`, is a valid jump destination. -/
theorem jumpDest_l1Entry (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (4215 + 38 * (k - 1)) = true := by
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

end Challenge.Modexp.Submission.Proofs.Fast.KernelChain
