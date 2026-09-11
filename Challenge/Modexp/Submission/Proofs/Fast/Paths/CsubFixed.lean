import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open YulEvmCompiler

/-- All widths share the proved conditional-subtraction loop. -/
def csGenericPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3754 .JUMPDEST,
   pushAt 3755 2 9440,
   opAt 3756 .MLOAD,
   pushAt 3757 2 9408,
   opAt 3758 .MLOAD,
   opAt 3759 (.Dup ⟨0, by decide⟩),
   pushAt 3760 2 7168,
   opAt 3761 .ADD,
   opAt 3762 (.Swap ⟨0, by decide⟩),
   pushAt 3763 0 0,
   opAt 3764 (.Swap ⟨2, by decide⟩),
   pushAt 3765 2 2144,
   opAt 3766 .JUMP]

@[simp] theorem csGenericPC3754 : Artifact.submissionArtifact.instructionPC 3754 = 4930 := by rfl
@[simp] theorem csGenericPC3755 : Artifact.submissionArtifact.instructionPC 3755 = 4931 := by rfl
@[simp] theorem csGenericPC3756 : Artifact.submissionArtifact.instructionPC 3756 = 4934 := by rfl
@[simp] theorem csGenericPC3757 : Artifact.submissionArtifact.instructionPC 3757 = 4935 := by rfl
@[simp] theorem csGenericPC3758 : Artifact.submissionArtifact.instructionPC 3758 = 4938 := by rfl
@[simp] theorem csGenericPC3759 : Artifact.submissionArtifact.instructionPC 3759 = 4939 := by rfl
@[simp] theorem csGenericPC3760 : Artifact.submissionArtifact.instructionPC 3760 = 4940 := by rfl
@[simp] theorem csGenericPC3761 : Artifact.submissionArtifact.instructionPC 3761 = 4943 := by rfl
@[simp] theorem csGenericPC3762 : Artifact.submissionArtifact.instructionPC 3762 = 4944 := by rfl
@[simp] theorem csGenericPC3763 : Artifact.submissionArtifact.instructionPC 3763 = 4945 := by rfl
@[simp] theorem csGenericPC3764 : Artifact.submissionArtifact.instructionPC 3764 = 4946 := by rfl
@[simp] theorem csGenericPC3765 : Artifact.submissionArtifact.instructionPC 3765 = 4947 := by rfl
@[simp] theorem csGenericPC3766 : Artifact.submissionArtifact.instructionPC 3766 = 4950 := by rfl

end Challenge.Modexp.Submission.Proofs.Fast
