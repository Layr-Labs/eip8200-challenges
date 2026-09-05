import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2State
import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Paths

set_option warningAsError true
set_option maxRecDepth 50000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Branch

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardEip2Logic GuardEip2State GuardEip2Paths

theorem run_iszero_match (input : ByteArray) (h : guardDiff input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchIsZeroPath
      (accState input 4969 (acc2 input)) =
      some (conditionState input 4970 (UInt256.ofNat 1)) := by
  have hzero : UInt256.isZero (acc2 input) = UInt256.ofNat 1 := by
    rw [acc2_eq_guardDiff]; exact diff_isZero_one input h
  have hpc : (accState input 4969 (acc2 input)).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2230 := by
    simp [accState, initialState, gEip2PC0, gEip2PC1, gEip2PC2, Challenge.EvmProof.Word.word_toNat_ofNat]
  have hop : Challenge.EvmProof.Stepper.runLocated branchIsZeroLocated
      (accState input 4969 (acc2 input)) =
      some (conditionState input 4970 (UInt256.ofNat 1)) := by
    unfold Challenge.EvmProof.Stepper.runLocated
    change (if (accState input 4969 (acc2 input)).pc.toNat =
        Artifact.submissionArtifact.instructionPC 2230 then
        Challenge.EvmProof.Stepper.runInstr (.op .ISZERO)
          (accState input 4969 (acc2 input)) else none) = _
    rw [if_pos hpc]
    unfold Challenge.EvmProof.Stepper.runInstr
    rw [if_pos (by simp [accState])]
    simp only [accState, conditionState, hzero, Challenge.EvmProof.Word.succ_ofNat_mod]
  simp only [branchIsZeroPath, Challenge.EvmProof.Stepper.runLocatedBlock, hop]

theorem run_iszero_mismatch (input : ByteArray) (h : guardDiff input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchIsZeroPath
      (accState input 4969 (acc2 input)) =
      some (conditionState input 4970 (UInt256.ofNat 0)) := by
  have hzero : UInt256.isZero (acc2 input) = UInt256.ofNat 0 := by
    rw [acc2_eq_guardDiff]; exact diff_isZero_zero input h
  have hpc : (accState input 4969 (acc2 input)).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2230 := by
    simp [accState, initialState, gEip2PC0, gEip2PC1, gEip2PC2, Challenge.EvmProof.Word.word_toNat_ofNat]
  have hop : Challenge.EvmProof.Stepper.runLocated branchIsZeroLocated
      (accState input 4969 (acc2 input)) =
      some (conditionState input 4970 (UInt256.ofNat 0)) := by
    unfold Challenge.EvmProof.Stepper.runLocated
    change (if (accState input 4969 (acc2 input)).pc.toNat =
        Artifact.submissionArtifact.instructionPC 2230 then
        Challenge.EvmProof.Stepper.runInstr (.op .ISZERO)
          (accState input 4969 (acc2 input)) else none) = _
    rw [if_pos hpc]
    unfold Challenge.EvmProof.Stepper.runInstr
    rw [if_pos (by simp [accState])]
    simp only [accState, conditionState, hzero, Challenge.EvmProof.Word.succ_ofNat_mod]
  simp only [branchIsZeroPath, Challenge.EvmProof.Stepper.runLocatedBlock, hop]

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Branch
