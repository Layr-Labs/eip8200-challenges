import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
set_option maxRecDepth 40000
namespace CycleSubmission.Global.ZeroShiftTailPCs
@[simp] theorem pc8382 : CycleSubmission.Artifact.artifact.instructionPC 8280 = 10822 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem pc8384 : CycleSubmission.Artifact.artifact.instructionPC 8282 = 10824 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
end CycleSubmission.Global.ZeroShiftTailPCs
