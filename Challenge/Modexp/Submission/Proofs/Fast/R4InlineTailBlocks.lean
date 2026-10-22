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

def block_tail : Block Artifact.submissionArtifact .Osaka 9688 prog_tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7605 3 9688 prog_tail
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7605 + 3 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 664 9688 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 664 3 prog_tail rfl) (by decide)

def block_st4 : Block Artifact.submissionArtifact .Osaka 9693 prog_st4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7608 9 9693 prog_st4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7608 + 9 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 667 9693 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 667 9 prog_st4 rfl) (by decide)

def block_branch : Block Artifact.submissionArtifact .Osaka 9710 prog_branch :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7617 8 9710 prog_branch
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7617 + 8 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 676 9710 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 676 8 prog_branch rfl) (by decide)

def block_m4 : Block Artifact.submissionArtifact .Osaka 9720 prog_m4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7625 8 9720 prog_m4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7625 + 8 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 684 9720 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 684 8 prog_m4 rfl) (by decide)

def block_rare4 : Block Artifact.submissionArtifact .Osaka 9730 prog_rare4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7633 46 9730 prog_rare4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7633 + 46 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 692 9730 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 692 46 prog_rare4 rfl) (by decide)
theorem jd4280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 8998 = true :=
  Artifact.isValidJumpDest_index 6941 (by rfl)
theorem jd4731 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 9693 = true :=
  Artifact.isValidJumpDest_index 7608 (by rfl)
theorem jd4768 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 9730 = true :=
  Artifact.isValidJumpDest_index 7633 (by rfl)
end Challenge.Modexp.Submission.Proofs.Fast.R4InlineTailBlocks
