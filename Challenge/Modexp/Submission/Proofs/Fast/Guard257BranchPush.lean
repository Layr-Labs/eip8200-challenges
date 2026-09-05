import Challenge.Modexp.Submission.Proofs.Fast.Guard257State
import Challenge.Modexp.Submission.Proofs.Fast.Guard257Paths

set_option warningAsError true
set_option maxRecDepth 50000
namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Branch

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard257State Guard257Paths

theorem run_push (input : ByteArray) (condition : UInt256) :
    Challenge.EvmProof.Stepper.runLocated branchPushLocated
      (conditionState input 4898 condition) =
      some (jumpStackState input condition) := by
  have hpc : (conditionState input 4898 condition).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2182 := by
    simp [conditionState, initialState, g257PC0, g257PC1, g257PC2, Challenge.EvmProof.Word.word_toNat_ofNat]
  unfold Challenge.EvmProof.Stepper.runLocated
  change (if (conditionState input 4898 condition).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2182 then
      Challenge.EvmProof.Stepper.runInstr (.push 2 (UInt256.ofNat 4906))
        (conditionState input 4898 condition) else none) = _
  rw [if_pos hpc]
  have hcap : (conditionState input 4898 condition).stack.length < 1024 := by
    simp [conditionState]
  have hwidth : ¬ (2 : Fin 33).val = 0 := by decide
  have hthree : (2 : Fin 33).val + 1 = 3 := by decide
  have hadd : UInt256.ofNat 4898 + UInt256.ofNat 3 = UInt256.ofNat 4901 :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos hcap]
  simp only
  rw [if_neg hwidth]
  simp only [conditionState, jumpStackState, hthree, hadd]

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Branch
