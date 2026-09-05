import Challenge.Modexp.Submission.Proofs.Fast.Guard1024State
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Paths

set_option warningAsError true
set_option maxRecDepth 50000
namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024Branch

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard1024Logic Guard1024State Guard1024Paths

theorem run_iszero_match (input : ByteArray) (h : guardDiff input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchIsZeroPath
      (accState input 4681 (acc3 input)) =
      some (conditionState input 4682 (UInt256.ofNat 1)) := by
  have hzero : UInt256.isZero (acc3 input) = UInt256.ofNat 1 := by
    rw [acc3_eq_guardDiff]
    exact diff_isZero_one input h
  have hpc : (accState input 4681 (acc3 input)).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2118 := by
    simp [accState, initialState, guardPC1,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hop : Challenge.EvmProof.Stepper.runLocated branchIsZeroLocated
      (accState input 4681 (acc3 input)) =
      some (conditionState input 4682 (UInt256.ofNat 1)) := by
    unfold Challenge.EvmProof.Stepper.runLocated
    change (if (accState input 4681 (acc3 input)).pc.toNat =
        Artifact.submissionArtifact.instructionPC 2118 then
        Challenge.EvmProof.Stepper.runInstr (.op .ISZERO)
          (accState input 4681 (acc3 input)) else none) = _
    rw [if_pos hpc]
    unfold Challenge.EvmProof.Stepper.runInstr
    rw [if_pos (by simp [accState])]
    simp only [accState, conditionState, hzero,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  simp only [branchIsZeroPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, hop]

theorem run_iszero_mismatch (input : ByteArray) (h : guardDiff input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchIsZeroPath
      (accState input 4681 (acc3 input)) =
      some (conditionState input 4682 (UInt256.ofNat 0)) := by
  have hzero : UInt256.isZero (acc3 input) = UInt256.ofNat 0 := by
    rw [acc3_eq_guardDiff]
    exact diff_isZero_zero input h
  have hpc : (accState input 4681 (acc3 input)).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2118 := by
    simp [accState, initialState, guardPC1,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hop : Challenge.EvmProof.Stepper.runLocated branchIsZeroLocated
      (accState input 4681 (acc3 input)) =
      some (conditionState input 4682 (UInt256.ofNat 0)) := by
    unfold Challenge.EvmProof.Stepper.runLocated
    change (if (accState input 4681 (acc3 input)).pc.toNat =
        Artifact.submissionArtifact.instructionPC 2118 then
        Challenge.EvmProof.Stepper.runInstr (.op .ISZERO)
          (accState input 4681 (acc3 input)) else none) = _
    rw [if_pos hpc]
    unfold Challenge.EvmProof.Stepper.runInstr
    rw [if_pos (by simp [accState])]
    simp only [accState, conditionState, hzero,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  simp only [branchIsZeroPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, hop]

end Challenge.Modexp.Submission.Proofs.Fast.Guard1024Branch
