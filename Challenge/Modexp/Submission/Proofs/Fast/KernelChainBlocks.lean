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

def l1Block1 : Block Artifact.submissionArtifact .Osaka 3761 (stepProgram 192 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2811 31 3761 (stepProgram 192 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block2 : Block Artifact.submissionArtifact .Osaka 3798 (stepProgram 160 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2842 31 3798 (stepProgram 160 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block3 : Block Artifact.submissionArtifact .Osaka 3835 (stepProgram 128 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2873 31 3835 (stepProgram 128 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block4 : Block Artifact.submissionArtifact .Osaka 3872 (stepProgram 96 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2904 31 3872 (stepProgram 96 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block5 : Block Artifact.submissionArtifact .Osaka 3909 (stepProgram 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2935 31 3909 (stepProgram 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block6 : Block Artifact.submissionArtifact .Osaka 3946 (stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2966 31 3946 (stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block7 : Block Artifact.submissionArtifact .Osaka 3983 (stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2997 31 3983 (stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

/-! ## Jump destinations of the chain entries (block `k` for `k = 1..7`, and the
middle `JUMPDEST` = entry `k = 8`) -/

theorem jumpDest4068 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3761 = true :=
  Artifact.isValidJumpDest_index 2811 (by rfl)
theorem jumpDest4106 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3798 = true :=
  Artifact.isValidJumpDest_index 2842 (by rfl)
theorem jumpDest4144 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3835 = true :=
  Artifact.isValidJumpDest_index 2873 (by rfl)
theorem jumpDest4182 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3872 = true :=
  Artifact.isValidJumpDest_index 2904 (by rfl)
theorem jumpDest4220 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3909 = true :=
  Artifact.isValidJumpDest_index 2935 (by rfl)
theorem jumpDest4258 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3946 = true :=
  Artifact.isValidJumpDest_index 2966 (by rfl)
theorem jumpDest4296 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3983 = true :=
  Artifact.isValidJumpDest_index 2997 (by rfl)
theorem jumpDest4334 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4020 = true :=
  Artifact.isValidJumpDest_index 3028 (by rfl)

/-- Every chain entry `4296 + 37(k-1)`, `1 ≤ k ≤ 8`, is a valid jump destination. -/
theorem jumpDest_l1Entry (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (3761 + 37 * (k - 1)) = true := by
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
