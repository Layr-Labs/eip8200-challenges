import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The first seven bit bodies retain seventeen instructions each; the last retains fifteen. Certificate names are stable API names, while their indices and PCs bind the selected artifact.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

open YulEvmCompiler

@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 151 = 220 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 152 = 223 := by rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 1886 = 2505 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 1887 = 2506 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 1888 = 2508 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 1889 = 2509 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 1980 = 2616 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 1981 = 2617 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 1982 = 2619 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
