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

@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 152 = 227 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 153 = 230 := by rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 1893 = 2544 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 1894 = 2545 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 1895 = 2547 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 1896 = 2548 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 1987 = 2655 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 1988 = 2656 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 1989 = 2659 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
