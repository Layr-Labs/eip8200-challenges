import Challenge.Modexp.Submission.Proofs.Fast.Guard1024BranchPush

set_option warningAsError true
set_option maxRecDepth 50000
namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024Branch

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard1024State Guard1024Paths

theorem run_jump_notTaken (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated branchJumpLocated
      (jumpStackState input (UInt256.ofNat 0)) = some (branchState input 4686) := by
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hpc : (jumpStackState input (UInt256.ofNat 0)).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2120 := by
    simp [jumpStackState, initialState, guardPC1,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  unfold Challenge.EvmProof.Stepper.runLocated
  change (if (jumpStackState input (UInt256.ofNat 0)).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2120 then
      Challenge.EvmProof.Stepper.runInstr (.op .JUMPI)
        (jumpStackState input (UInt256.ofNat 0)) else none) = _
  rw [if_pos hpc]
  have hcap : (jumpStackState input (UInt256.ofNat 0)).stack.length < 1024 := by
    simp [jumpStackState]
  have hsucc : (UInt256.ofNat 4685).succ = UInt256.ofNat 4686 :=
    Challenge.EvmProof.Word.succ_ofNat (by norm_num)
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos hcap]
  simp only
  simp only [jumpStackState]
  rw [if_neg hfalse]
  simp only [branchState, hsucc]
  rw [show (initialState submissionBytecode input 0).stack = [] by rfl]

end Challenge.Modexp.Submission.Proofs.Fast.Guard1024Branch
