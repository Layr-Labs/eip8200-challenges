import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open YulEvmCompiler

/-- All widths share the proved conditional-subtraction loop. -/
def csGenericPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3758 .JUMPDEST,
   pushAt 3759 2 9440,
   opAt 3760 .MLOAD,
   pushAt 3761 2 9408,
   opAt 3762 .MLOAD,
   opAt 3763 (.Dup ⟨0, by decide⟩),
   pushAt 3764 2 7168,
   opAt 3765 .ADD,
   opAt 3766 (.Swap ⟨0, by decide⟩),
   pushAt 3767 0 0,
   opAt 3768 (.Swap ⟨2, by decide⟩),
   pushAt 3769 2 2144,
   opAt 3770 .JUMP]

@[simp] theorem csGenericPC3754 : Artifact.submissionArtifact.instructionPC 3758 = 4930 := by rfl
@[simp] theorem csGenericPC3755 : Artifact.submissionArtifact.instructionPC 3759 = 4931 := by rfl
@[simp] theorem csGenericPC3756 : Artifact.submissionArtifact.instructionPC 3760 = 4934 := by rfl
@[simp] theorem csGenericPC3757 : Artifact.submissionArtifact.instructionPC 3761 = 4935 := by rfl
@[simp] theorem csGenericPC3758 : Artifact.submissionArtifact.instructionPC 3762 = 4938 := by rfl
@[simp] theorem csGenericPC3759 : Artifact.submissionArtifact.instructionPC 3763 = 4939 := by rfl
@[simp] theorem csGenericPC3760 : Artifact.submissionArtifact.instructionPC 3764 = 4940 := by rfl
@[simp] theorem csGenericPC3761 : Artifact.submissionArtifact.instructionPC 3765 = 4943 := by rfl
@[simp] theorem csGenericPC3762 : Artifact.submissionArtifact.instructionPC 3766 = 4944 := by rfl
@[simp] theorem csGenericPC3763 : Artifact.submissionArtifact.instructionPC 3767 = 4945 := by rfl
@[simp] theorem csGenericPC3764 : Artifact.submissionArtifact.instructionPC 3768 = 4946 := by rfl
@[simp] theorem csGenericPC3765 : Artifact.submissionArtifact.instructionPC 3769 = 4947 := by rfl
@[simp] theorem csGenericPC3766 : Artifact.submissionArtifact.instructionPC 3770 = 4950 := by rfl

end Challenge.Modexp.Submission.Proofs.Fast
