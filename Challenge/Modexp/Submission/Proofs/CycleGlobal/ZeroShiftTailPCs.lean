import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
set_option maxRecDepth 40000
namespace CycleSubmission.Global.ZeroShiftTailPCs
@[simp] theorem pc8382 : CycleSubmission.Artifact.artifact.instructionPC 8383 = 10927 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem pc8384 : CycleSubmission.Artifact.artifact.instructionPC 8385 = 10929 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
end CycleSubmission.Global.ZeroShiftTailPCs
