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

@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 536 = 688 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 537 = 691 := by rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2323 = 3078 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2324 = 3079 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2325 = 3081 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2326 = 3082 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2417 = 3189 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2418 = 3190 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2419 = 3193 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
