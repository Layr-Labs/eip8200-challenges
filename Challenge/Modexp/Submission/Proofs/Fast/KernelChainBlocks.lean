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

def l1Block1 : Block Artifact.submissionArtifact .Osaka 3510 (stepProgram 192 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2806 31 3510 (stepProgram 192 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block2 : Block Artifact.submissionArtifact .Osaka 3547 (stepProgram 160 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2837 31 3547 (stepProgram 160 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block3 : Block Artifact.submissionArtifact .Osaka 3584 (stepProgram 128 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2868 31 3584 (stepProgram 128 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block4 : Block Artifact.submissionArtifact .Osaka 3621 (stepProgram 96 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2899 31 3621 (stepProgram 96 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block5 : Block Artifact.submissionArtifact .Osaka 3658 (stepProgram 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2930 31 3658 (stepProgram 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block6 : Block Artifact.submissionArtifact .Osaka 3695 (stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2961 31 3695 (stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block7 : Block Artifact.submissionArtifact .Osaka 3732 (stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2992 31 3732 (stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

/-! ## The private four-limb ladder copy (5172-5313)

The four-limb multiply rows no longer share the ladder at 3528: the setup computes
`ent = 5172`, the entry of a byte copy of 3528-3665 that keeps its own tail jump.  Because
the copy is byte-identical, blocks k5..k7 reuse the very same `stepProgram` literals -- only
the instruction indices and program counters differ. -/

def l1Block5Copy : Block Artifact.submissionArtifact .Osaka 5296 (stepProgram 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4262 31 5296 (stepProgram 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block6Copy : Block Artifact.submissionArtifact .Osaka 5333 (stepProgram 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4293 31 5333 (stepProgram 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Block7Copy : Block Artifact.submissionArtifact .Osaka 5370 (stepProgram 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4324 31 5370 (stepProgram 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest5172 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5296 = true :=
  Artifact.isValidJumpDest_index 4262 (by rfl)
theorem jumpDest5209 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5333 = true :=
  Artifact.isValidJumpDest_index 4293 (by rfl)
theorem jumpDest5246 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5370 = true :=
  Artifact.isValidJumpDest_index 4324 (by rfl)

/-! ## Jump destinations of the chain entries (block `k` for `k = 1..7`, and the
middle `JUMPDEST` = entry `k = 8`) -/

theorem jumpDest4068 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3510 = true :=
  Artifact.isValidJumpDest_index 2806 (by rfl)
theorem jumpDest4106 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3547 = true :=
  Artifact.isValidJumpDest_index 2837 (by rfl)
theorem jumpDest4144 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3584 = true :=
  Artifact.isValidJumpDest_index 2868 (by rfl)
theorem jumpDest4182 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3621 = true :=
  Artifact.isValidJumpDest_index 2899 (by rfl)
theorem jumpDest4220 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3658 = true :=
  Artifact.isValidJumpDest_index 2930 (by rfl)
theorem jumpDest4258 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3695 = true :=
  Artifact.isValidJumpDest_index 2961 (by rfl)
theorem jumpDest4296 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3732 = true :=
  Artifact.isValidJumpDest_index 2992 (by rfl)
theorem jumpDest4334 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3769 = true :=
  Artifact.isValidJumpDest_index 3023 (by rfl)

/-- Every chain entry `3510 + 37(k-1)`, `1 ≤ k ≤ 8`, is a valid jump destination.
Base transcribed: the eight cited theorems prove pcs 3510 3547 3584 3621 3658 3695
3732 3769, all confirmed JUMPDESTs; 3510 is also `l1Target 8` / `l1BaseNat 8`. -/
theorem jumpDest_l1Entry (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (3510 + 37 * (k - 1)) = true := by
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

/-- The copy's middle-block entry, pc 5397 (= `5148 + 37*7`). -/
theorem jumpDest5283 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5407 = true :=
  Artifact.isValidJumpDest_index 4355 (by rfl)

/-- Every chain entry of the private four-limb ladder copy, `5148 + 37(k-1)` for
`5 ≤ k ≤ 8`, is a valid jump destination -- the mirror of `jumpDest_l1Entry`. -/
theorem jumpDest_l1EntryCopy (k : Nat) (hk5 : 5 ≤ k) (hk8 : k ≤ 8) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (5148 + 37 * (k - 1)) = true := by
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
