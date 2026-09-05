import Challenge.Modexp.Submission.Proofs.Fast.GuardState
import Challenge.Modexp.Submission.Proofs.Fast.GuardPaths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardFallback

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardState GuardPaths

private def fallbackMidState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 3920
      stack := [UInt256.ofNat 1314] }

theorem run_fallback_push (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated fallbackPushLocated
      (branchState input 3917) = some (fallbackMidState input) := by
  have hpc : (branchState input 3917).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2022 := by
    simp [branchState, initialState, guardPC3,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  unfold Challenge.EvmProof.Stepper.runLocated
  rw [fallbackPush_index, fallbackPush_instruction, if_pos hpc]
  have hcap : (branchState input 3917).stack.length < 1024 := by
    change [].length < 1024
    decide
  have hwidth : ¬ (2 : Fin 33).val = 0 := by decide
  have hthree : (2 : Fin 33).val + 1 = 3 := by decide
  have hadd : UInt256.ofNat 3917 + UInt256.ofNat 3 = UInt256.ofNat 3920 :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos hcap]
  simp only
  rw [if_neg hwidth]
  simp only [branchState, fallbackMidState, hthree, hadd]
  rw [show (initialState submissionBytecode input 0).stack = [] by rfl]

theorem run_fallback_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated fallbackJumpLocated
      (fallbackMidState input) = some (fallbackState input) := by
  have hpc : (fallbackMidState input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2023 := by
    simp [fallbackMidState, initialState, guardPC3,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hcap : (fallbackMidState input).stack.length < 1024 := by
    simp [fallbackMidState]
  have hjump : Decode.isValidJumpDest submissionBytecode 1314 = true :=
    Artifact.isValidJumpDest_index 977 (by rfl)
  unfold Challenge.EvmProof.Stepper.runLocated
  rw [fallbackJump_index, fallbackJump_instruction, if_pos hpc]
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos hcap]
  simp only [fallbackMidState]
  rw [show (UInt256.ofNat 1314).toNat = 1314 by decide,
    show (initialState submissionBytecode input 0).executionEnv.code =
      submissionBytecode by rfl, hjump]
  simp only [if_true, fallbackState, Main.trampolineState]
  rw [show (initialState submissionBytecode input 0).stack = [] by rfl]

theorem run_fallback (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock fallbackPath (branchState input 3917) =
      some (fallbackState input) := by
  unfold fallbackPath Challenge.EvmProof.Stepper.runLocatedBlock
  rw [run_fallback_push]
  change (match (fallbackMidState input).halt with
    | .Running => Challenge.EvmProof.Stepper.runLocatedBlock
        [fallbackJumpLocated] (fallbackMidState input)
    | _ => none) = _
  rw [show (fallbackMidState input).halt = .Running by rfl]
  unfold Challenge.EvmProof.Stepper.runLocatedBlock
  rw [run_fallback_jump]

end Challenge.Modexp.Submission.Proofs.Fast.GuardFallback
