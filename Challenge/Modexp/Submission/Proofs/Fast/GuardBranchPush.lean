import Challenge.Modexp.Submission.Proofs.Fast.GuardState
import Challenge.Modexp.Submission.Proofs.Fast.GuardPaths

set_option warningAsError true
set_option maxRecDepth 50000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardBranch

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardState GuardPaths

theorem run_push (input : ByteArray) (condition : UInt256) :
    Challenge.EvmProof.Stepper.runLocated branchPushLocated
      (conditionState input 3913 condition) =
      some (jumpStackState input condition) := by
  have hpc : (conditionState input 3913 condition).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2020 := by
    simp [conditionState, initialState, guardPC3,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hop : Challenge.EvmProof.Stepper.runLocated branchPushLocated
      (conditionState input 3913 condition) =
      some (jumpStackState input condition) := by
    unfold Challenge.EvmProof.Stepper.runLocated
    change (if (conditionState input 3913 condition).pc.toNat =
        Artifact.submissionArtifact.instructionPC 2020 then
        Challenge.EvmProof.Stepper.runInstr (.push 2 (UInt256.ofNat 3921))
          (conditionState input 3913 condition) else none) = _
    rw [if_pos hpc]
    have hcap : (conditionState input 3913 condition).stack.length < 1024 := by
      simp [conditionState]
    have hwidth : ¬ (2 : Fin 33).val = 0 := by decide
    have hthree : (2 : Fin 33).val + 1 = 3 := by decide
    have hadd : UInt256.ofNat 3913 + UInt256.ofNat 3 = UInt256.ofNat 3916 :=
      Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
    unfold Challenge.EvmProof.Stepper.runInstr
    rw [if_pos hcap]
    simp only
    rw [if_neg hwidth]
    simp only [conditionState, jumpStackState, hthree, hadd]
  exact hop

end Challenge.Modexp.Submission.Proofs.Fast.GuardBranch
