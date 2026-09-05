import Challenge.Modexp.Submission.Proofs.Fast.GuardBranchPush

set_option warningAsError true
set_option maxRecDepth 50000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardBranch

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardState GuardPaths

theorem run_jump_taken (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated branchJumpLocated
      (jumpStackState input (UInt256.ofNat 1)) = some (branchState input 3921) := by
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode 3921 = true :=
    Artifact.isValidJumpDest_index 2024 (by rfl)
  have hpc : (jumpStackState input (UInt256.ofNat 1)).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2021 := by
    simp [jumpStackState, initialState, guardPC3,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  unfold Challenge.EvmProof.Stepper.runLocated
  change (if (jumpStackState input (UInt256.ofNat 1)).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2021 then
      Challenge.EvmProof.Stepper.runInstr (.op .JUMPI)
        (jumpStackState input (UInt256.ofNat 1)) else none) = _
  rw [if_pos hpc]
  have hcap : (jumpStackState input (UInt256.ofNat 1)).stack.length < 1024 := by
    simp [jumpStackState]
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos hcap]
  simp only
  simp only [jumpStackState]
  rw [if_pos htrue]
  rw [show (UInt256.ofNat 3921).toNat = 3921 by decide]
  rw [show (initialState submissionBytecode input 0).executionEnv.code =
    submissionBytecode by rfl, hjump]
  simp only [if_true, branchState]
  rw [show (initialState submissionBytecode input 0).stack = [] by rfl]

end Challenge.Modexp.Submission.Proofs.Fast.GuardBranch
