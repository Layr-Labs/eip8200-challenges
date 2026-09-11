import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open YulEvmCompiler

/-- All widths share the proved conditional-subtraction loop. -/
def csGenericPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3745 .JUMPDEST,
   pushAt 3746 2 9440,
   opAt 3747 .MLOAD,
   pushAt 3748 2 9408,
   opAt 3749 .MLOAD,
   opAt 3750 (.Dup ⟨0, by decide⟩),
   pushAt 3751 2 7168,
   opAt 3752 .ADD,
   opAt 3753 (.Swap ⟨0, by decide⟩),
   pushAt 3754 0 0,
   opAt 3755 (.Swap ⟨2, by decide⟩),
   pushAt 3756 2 2144,
   opAt 3757 .JUMP]

@[simp] theorem csGenericPC3754 : Artifact.submissionArtifact.instructionPC 3745 = 4926 := by rfl
@[simp] theorem csGenericPC3755 : Artifact.submissionArtifact.instructionPC 3746 = 4927 := by rfl
@[simp] theorem csGenericPC3756 : Artifact.submissionArtifact.instructionPC 3747 = 4930 := by rfl
@[simp] theorem csGenericPC3757 : Artifact.submissionArtifact.instructionPC 3748 = 4931 := by rfl
@[simp] theorem csGenericPC3758 : Artifact.submissionArtifact.instructionPC 3749 = 4934 := by rfl
@[simp] theorem csGenericPC3759 : Artifact.submissionArtifact.instructionPC 3750 = 4935 := by rfl
@[simp] theorem csGenericPC3760 : Artifact.submissionArtifact.instructionPC 3751 = 4936 := by rfl
@[simp] theorem csGenericPC3761 : Artifact.submissionArtifact.instructionPC 3752 = 4939 := by rfl
@[simp] theorem csGenericPC3762 : Artifact.submissionArtifact.instructionPC 3753 = 4940 := by rfl
@[simp] theorem csGenericPC3763 : Artifact.submissionArtifact.instructionPC 3754 = 4941 := by rfl
@[simp] theorem csGenericPC3764 : Artifact.submissionArtifact.instructionPC 3755 = 4942 := by rfl
@[simp] theorem csGenericPC3765 : Artifact.submissionArtifact.instructionPC 3756 = 4943 := by rfl
@[simp] theorem csGenericPC3766 : Artifact.submissionArtifact.instructionPC 3757 = 4946 := by rfl

end Challenge.Modexp.Submission.Proofs.Fast
