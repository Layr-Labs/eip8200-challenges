import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the exponent-bit block

The block is entered by the jump at pc 206, derives `base - 1` at pcs 2372 to 2376,
runs one bit body per iteration from the head at 2377, and leaves through the exit at
pcs 2413 to 2416 back to the byte loop at 210. Certificate names are stable API names,
while their indices and PCs bind the selected artifact.
-/

namespace CycleSubmission.Global.UnrollPCs
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM

open YulEvmCompiler

@[simp] theorem pc485 : CycleSubmission.Artifact.artifact.instructionPC 133 = 203 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc486 : CycleSubmission.Artifact.artifact.instructionPC 134 = 206 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2414 : CycleSubmission.Artifact.artifact.instructionPC 3037 = 3962 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2415 : CycleSubmission.Artifact.artifact.instructionPC 3038 = 3963 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2416 : CycleSubmission.Artifact.artifact.instructionPC 3039 = 3965 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2417 : CycleSubmission.Artifact.artifact.instructionPC 3040 = 3966 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2554 : CycleSubmission.Artifact.artifact.instructionPC 3069 = 4002 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2555 : CycleSubmission.Artifact.artifact.instructionPC 3070 = 4003 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2556 : CycleSubmission.Artifact.artifact.instructionPC 3071 = 4006 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

end CycleSubmission.Global.UnrollPCs
