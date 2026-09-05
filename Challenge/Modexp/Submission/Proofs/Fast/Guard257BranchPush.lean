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
      (conditionState input 4980 condition) =
      some (jumpStackState input condition) := by
  have hpc : (conditionState input 4980 condition).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2176 := by
    simp [conditionState, initialState, guard257PC1,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hop : Challenge.EvmProof.Stepper.runLocated branchPushLocated
      (conditionState input 4980 condition) =
      some (jumpStackState input condition) := by
    unfold Challenge.EvmProof.Stepper.runLocated
    change (if (conditionState input 4980 condition).pc.toNat =
        Artifact.submissionArtifact.instructionPC 2176 then
        Challenge.EvmProof.Stepper.runInstr (.push 2 (UInt256.ofNat 4988))
          (conditionState input 4980 condition) else none) = _
    rw [if_pos hpc]
    have hcap : (conditionState input 4980 condition).stack.length < 1024 := by
      simp [conditionState]
    have hwidth : ¬ (2 : Fin 33).val = 0 := by decide
    have hthree : (2 : Fin 33).val + 1 = 3 := by decide
    have hadd : UInt256.ofNat 4980 + UInt256.ofNat 3 = UInt256.ofNat 4983 :=
      Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
    unfold Challenge.EvmProof.Stepper.runInstr
    rw [if_pos hcap]
    simp only
    rw [if_neg hwidth]
    simp only [conditionState, jumpStackState, hthree, hadd]
  exact hop

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Branch
