import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the exponent-bit block

The block is entered by the jump at pc 206, derives `base - 1` at pcs 2360 to 2364,
runs one bit body per iteration from the head at 2365, and leaves through the exit at
pcs 2401 to 2404 back to the byte loop at 210. Certificate names are stable API names,
while their indices and PCs bind the selected artifact.
-/
namespace CycleSubmission.Global.UnrollPCs
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
@[simp] theorem pc485 : CycleSubmission.Artifact.artifact.instructionPC 131 = 170 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc486 : CycleSubmission.Artifact.artifact.instructionPC 132 = 173 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2414 : CycleSubmission.Artifact.artifact.instructionPC 7912 = 10463 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2415 : CycleSubmission.Artifact.artifact.instructionPC 7913 = 10464 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2416 : CycleSubmission.Artifact.artifact.instructionPC 7914 = 10466 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2417 : CycleSubmission.Artifact.artifact.instructionPC 7915 = 10467 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2554 : CycleSubmission.Artifact.artifact.instructionPC 7944 = 10503 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2555 : CycleSubmission.Artifact.artifact.instructionPC 7945 = 10504 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2556 : CycleSubmission.Artifact.artifact.instructionPC 7946 = 10507 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
end CycleSubmission.Global.UnrollPCs
