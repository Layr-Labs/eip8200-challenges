import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandL1
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

/-!
# The seven uniform first-loop blocks of the sqCP1m kernel (located)

Block `k = 1..7` is instruction `3189 + 32(k-1)`, 32 instructions, pc `4296 + 37(k-1)`,
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

def l1Block1 : Block Artifact.submissionArtifact .Osaka 3748 (stepProgram 192 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2772 31 3748 (stepProgram 192 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block2 : Block Artifact.submissionArtifact .Osaka 3785 (stepProgram 160 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2803 31 3785 (stepProgram 160 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block3 : Block Artifact.submissionArtifact .Osaka 3822 (stepProgram 128 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2834 31 3822 (stepProgram 128 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block4 : Block Artifact.submissionArtifact .Osaka 3859 (stepProgram 96 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2865 31 3859 (stepProgram 96 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block5 : Block Artifact.submissionArtifact .Osaka 3896 (stepProgram 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2896 31 3896 (stepProgram 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block6 : Block Artifact.submissionArtifact .Osaka 3933 (stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2927 31 3933 (stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block7 : Block Artifact.submissionArtifact .Osaka 3970 (stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2958 31 3970 (stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

/-! ## Jump destinations of the chain entries (block `k` for `k = 1..7`, and the
middle `JUMPDEST` = entry `k = 8`) -/

theorem jumpDest4068 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3748 = true :=
  Artifact.isValidJumpDest_index 2772 (by rfl)
theorem jumpDest4106 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3785 = true :=
  Artifact.isValidJumpDest_index 2803 (by rfl)
theorem jumpDest4144 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3822 = true :=
  Artifact.isValidJumpDest_index 2834 (by rfl)
theorem jumpDest4182 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3859 = true :=
  Artifact.isValidJumpDest_index 2865 (by rfl)
theorem jumpDest4220 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3896 = true :=
  Artifact.isValidJumpDest_index 2896 (by rfl)
theorem jumpDest4258 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3933 = true :=
  Artifact.isValidJumpDest_index 2927 (by rfl)
theorem jumpDest4296 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3970 = true :=
  Artifact.isValidJumpDest_index 2958 (by rfl)
theorem jumpDest4334 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4007 = true :=
  Artifact.isValidJumpDest_index 2989 (by rfl)

/-- Every chain entry `4296 + 37(k-1)`, `1 ≤ k ≤ 8`, is a valid jump destination. -/
theorem jumpDest_l1Entry (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (3748 + 37 * (k - 1)) = true := by
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
