import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineArtifactSuffix
import Challenge.Modexp.Submission.Proofs.Fast.R4SliceFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineTailPrograms
noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Global.Fast.R4InlineTailBlocks
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

def block_tail : Block CycleSubmission.Artifact.artifact .Osaka 4727 prog_tail :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3784 3 4727 prog_tail
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3784+3 ≤ 9167) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 664 4727 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 664 3 prog_tail rfl) (by decide)

def block_st4 : Block CycleSubmission.Artifact.artifact .Osaka 4732 prog_st4 :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3787 9 4732 prog_st4
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3787+9 ≤ 9167) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 667 4732 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 667 9 prog_st4 rfl) (by decide)

def block_branch : Block CycleSubmission.Artifact.artifact .Osaka 4749 prog_branch :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3796 6 4749 prog_branch
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3796+6 ≤ 9167) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 676 4749 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 676 6 prog_branch rfl) (by decide)

def block_m4 : Block CycleSubmission.Artifact.artifact .Osaka 4759 prog_m4 :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3802 8 4759 prog_m4
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3802+8 ≤ 9167) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 682 4759 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 682 8 prog_m4 rfl) (by decide)

def block_rare4 : Block CycleSubmission.Artifact.artifact .Osaka 4769 prog_rare4 :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3810 46 4769 prog_rare4
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3810+46 ≤ 9167) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 690 4769 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 690 46 prog_rare4 rfl) (by decide)
theorem jd4280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4037 = true :=
  CycleSubmission.Global.Binding.jumpDest 3120 (by rfl)
theorem jd4731 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4732 = true :=
  CycleSubmission.Global.Binding.jumpDest 3787 (by rfl)
theorem jd4768 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4769 = true :=
  CycleSubmission.Global.Binding.jumpDest 3810 (by rfl)
end CycleSubmission.Global.Fast.R4InlineTailBlocks
