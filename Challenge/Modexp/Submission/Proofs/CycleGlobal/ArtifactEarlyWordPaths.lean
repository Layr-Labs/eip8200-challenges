import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
noncomputable section
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CycleSubmission.Global.Paths
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_size : WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 0 EarlyWordProgram.sizeProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 0 9 0 EarlyWordProgram.sizeProgram
    (by change 0+9 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
structure EarlySizePaths (artifact : Challenge.EvmProof.ProgramArtifact) (fork : Fork) where
  size : WindowTwentyOneBinding.Block artifact fork 0 EarlyWordProgram.sizeProgram
  legacyJump : Decode.isValidJumpDest artifact.code 564 = true
def earlyWordPaths : EarlySizePaths CycleSubmission.Artifact.artifact .Osaka where
  size := earlyWord_size
  legacyJump := by exact CycleSubmission.Global.Binding.jumpDest 391 (by rfl)
open Challenge.EvmProof
open WindowTwentyOneEntry WindowTwentyOneBinding EarlyWordProgram
private theorem jump_env {artifact : ProgramArtifact} {fork : Fork} {template : State}
    (env : Environment artifact fork template) {pc : Nat}
    (hjump : Decode.isValidJumpDest artifact.code pc = true) :
    Decode.isValidJumpDest template.executionEnv.code pc = true := by
  rw [env.code]
  exact hjump
/-- An exponent or modulus size other than 32 (both within the EIP-7823 bound) reaches the fixed-vector recogniser's
entry at 599 with an empty stack. -/
def steps_size_miss {artifact : ProgramArtifact} {fork : Fork}
    (paths : EarlySizePaths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (he : exponentSize input ≤ 1024) (hm : modulusSize input ≤ 1024)
    (hmiss : ¬ (exponentSize input = 32 ∧ modulusSize input = 32)) :
    GasSteps (framed template (UInt256.ofNat 0) []) (framed template (UInt256.ofNat 564) []) := by
  have hs := run_size template input hdata (jump_env env paths.legacyJump)
  have hn : (sizeDiff input).toNat ≠ 0 := fun hz => hmiss ((sizeDiff_zero_iff input he hm).mp hz)
  rw [if_neg hn] at hs
  exact paths.size.steps (env.transfer (t := framed template (UInt256.ofNat 0) []) rfl rfl) rfl hs
/-- Exponent and modulus sizes 32 reach the base size test at 16 with an empty stack. -/
def steps_size_hit {artifact : ProgramArtifact} {fork : Fork}
    (paths : EarlySizePaths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hsize : exponentSize input = 32 ∧ modulusSize input = 32) :
    GasSteps (framed template (UInt256.ofNat 0) []) (framed template (UInt256.ofNat 16) []) := by
  have hs := run_size template input hdata (jump_env env paths.legacyJump)
  rw [if_pos (sizeDiff_zero_of input hsize)] at hs
  exact paths.size.steps (env.transfer (t := framed template (UInt256.ofNat 0) []) rfl rfl) rfl hs
end CycleSubmission.Global.Paths
