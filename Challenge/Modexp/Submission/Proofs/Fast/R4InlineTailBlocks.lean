import Challenge.Modexp.Submission.Proofs.Fast.R4InlineArtifactSuffix
import Challenge.Modexp.Submission.Proofs.Fast.R4SliceFast
import Challenge.Modexp.Submission.Proofs.Fast.R4InlineTailPrograms
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Fast.R4InlineTailBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

def block_tail : Block Artifact.submissionArtifact .Osaka 9687 prog_tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7604 3 9687 prog_tail
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7604 + 3 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 664 9687 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 664 3 prog_tail rfl) (by decide)

def block_st4 : Block Artifact.submissionArtifact .Osaka 9692 prog_st4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7607 9 9692 prog_st4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7607 + 9 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 667 9692 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 667 9 prog_st4 rfl) (by decide)

def block_branch : Block Artifact.submissionArtifact .Osaka 9709 prog_branch :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7616 8 9709 prog_branch
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7616 + 8 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 676 9709 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 676 8 prog_branch rfl) (by decide)

def block_m4 : Block Artifact.submissionArtifact .Osaka 9719 prog_m4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7624 8 9719 prog_m4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7624 + 8 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 684 9719 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 684 8 prog_m4 rfl) (by decide)

def block_rare4 : Block Artifact.submissionArtifact .Osaka 9729 prog_rare4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7632 46 9729 prog_rare4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7632 + 46 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 692 9729 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 692 46 prog_rare4 rfl) (by decide)
theorem jd4280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 8997 = true :=
  Artifact.isValidJumpDest_index 6940 (by rfl)
theorem jd4731 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 9692 = true :=
  Artifact.isValidJumpDest_index 7607 (by rfl)
theorem jd4768 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 9729 = true :=
  Artifact.isValidJumpDest_index 7632 (by rfl)
end Challenge.Modexp.Submission.Proofs.Fast.R4InlineTailBlocks
