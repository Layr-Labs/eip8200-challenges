import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Prepared.CombinedMemoGuard
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
namespace CycleSubmission.Global.Memo
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
def combinedBlock : WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 903 CycleSubmission.CombinedMemoGuard.program :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 638 17 903 CycleSubmission.CombinedMemoGuard.program
  (by change 638+17 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
theorem jumpDestLegacy : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 519 = true :=
 by
  have h := CycleSubmission.Global.Binding.jumpDest 357 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 357 = 519 := by
   rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem codeBound : CycleSubmission.Artifact.artifact.code.size < 2^256 := by
 rw [show CycleSubmission.Artifact.artifact.code = CycleSubmission.Artifact.bytecode from rfl,
  CycleSubmission.Artifact.bytecodeSize]
 decide
end CycleSubmission.Global.Memo
