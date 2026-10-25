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
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3793 3 4727 prog_tail
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3793 + 3 ≤ 9183) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 664 4727 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 664 3 prog_tail rfl) (by decide)

def block_st4 : Block CycleSubmission.Artifact.artifact .Osaka 4732 prog_st4 :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3796 9 4732 prog_st4
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3796 + 9 ≤ 9183) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 667 4732 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 667 9 prog_st4 rfl) (by decide)

def block_branch : Block CycleSubmission.Artifact.artifact .Osaka 4749 prog_branch :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3805 8 4749 prog_branch
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3805 + 8 ≤ 9183) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 676 4749 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 676 8 prog_branch rfl) (by decide)

def block_m4 : Block CycleSubmission.Artifact.artifact .Osaka 4759 prog_m4 :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3813 8 4759 prog_m4
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3813 + 8 ≤ 9183) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 684 4759 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 684 8 prog_m4 rfl) (by decide)

def block_rare4 : Block CycleSubmission.Artifact.artifact .Osaka 4769 prog_rare4 :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3821 46 4769 prog_rare4
    (by change _ ≤ CycleSubmission.Artifact.instructions.length; exact Nat.le_trans (by decide : 3821 + 46 ≤ 9183) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (R4InlineArtifactSuffix.pc 692 4769 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 692 46 prog_rare4 rfl) (by decide)
theorem jd4280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4037 = true :=
  CycleSubmission.Global.Binding.jumpDest 3129 (by rfl)
theorem jd4731 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4732 = true :=
  CycleSubmission.Global.Binding.jumpDest 3796 (by rfl)
theorem jd4768 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4769 = true :=
  CycleSubmission.Global.Binding.jumpDest 3821 (by rfl)
end CycleSubmission.Global.Fast.R4InlineTailBlocks
