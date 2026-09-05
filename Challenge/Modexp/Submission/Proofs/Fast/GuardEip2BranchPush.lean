import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2State
import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Paths

set_option warningAsError true
set_option maxRecDepth 50000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Branch

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardEip2State GuardEip2Paths

theorem run_push (input : ByteArray) (condition : UInt256) :
    Challenge.EvmProof.Stepper.runLocated branchPushLocated
      (conditionState input 5135 condition) =
      some (jumpStackState input condition) := by
  have hpc : (conditionState input 5135 condition).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2222 := by
    simp [conditionState, initialState, guardEip2PC0, guardEip2PC1, guardEip2PC2,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hop : Challenge.EvmProof.Stepper.runLocated branchPushLocated
      (conditionState input 5135 condition) =
      some (jumpStackState input condition) := by
    unfold Challenge.EvmProof.Stepper.runLocated
    change (if (conditionState input 5135 condition).pc.toNat =
        Artifact.submissionArtifact.instructionPC 2222 then
        Challenge.EvmProof.Stepper.runInstr (.push 2 (UInt256.ofNat 5143))
          (conditionState input 5135 condition) else none) = _
    rw [if_pos hpc]
    have hcap : (conditionState input 5135 condition).stack.length < 1024 := by
      simp [conditionState]
    have hwidth : ¬ (2 : Fin 33).val = 0 := by decide
    have hthree : (2 : Fin 33).val + 1 = 3 := by decide
    have hadd : UInt256.ofNat 5135 + UInt256.ofNat 3 = UInt256.ofNat 5138 :=
      Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
    unfold Challenge.EvmProof.Stepper.runInstr
    rw [if_pos hcap]
    simp only
    rw [if_neg hwidth]
    simp only [conditionState, jumpStackState, hthree, hadd]
  exact hop

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Branch
