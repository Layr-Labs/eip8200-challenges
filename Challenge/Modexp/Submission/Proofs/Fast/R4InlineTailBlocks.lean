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

def block_tail : Block Artifact.submissionArtifact .Osaka 9709 prog_tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7618 4 9709 prog_tail
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7618 + 4 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 677 9709 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 677 4 prog_tail rfl) (by decide)

def block_st4 : Block Artifact.submissionArtifact .Osaka 9715 prog_st4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7622 9 9715 prog_st4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7622 + 9 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 681 9715 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 681 9 prog_st4 rfl) (by decide)

def block_branch : Block Artifact.submissionArtifact .Osaka 9732 prog_branch :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7631 8 9732 prog_branch
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7631 + 8 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 690 9732 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 690 8 prog_branch rfl) (by decide)

def block_m4 : Block Artifact.submissionArtifact .Osaka 9742 prog_m4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7639 8 9742 prog_m4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7639 + 8 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 698 9742 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 698 8 prog_m4 rfl) (by decide)

def block_rare4 : Block Artifact.submissionArtifact .Osaka 9752 prog_rare4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7647 46 9752 prog_rare4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 7647 + 46 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (R4InlineArtifactSuffix.pc 706 9752 rfl) (by rw [R4SliceFast.locations_map]; exact R4InlineArtifactSuffix.slice 706 46 prog_rare4 rfl) (by decide)
theorem jd4280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 8998 = true :=
  Artifact.isValidJumpDest_index 6941 (by rfl)
theorem jd4731 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 9715 = true :=
  Artifact.isValidJumpDest_index 7622 (by rfl)
theorem jd4768 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 9752 = true :=
  Artifact.isValidJumpDest_index 7647 (by rfl)
end Challenge.Modexp.Submission.Proofs.Fast.R4InlineTailBlocks
