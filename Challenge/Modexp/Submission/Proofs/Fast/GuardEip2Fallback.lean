import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2State
import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Paths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Fallback

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardEip2State GuardEip2Paths

private def fallbackMidState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 5361
      stack := [UInt256.ofNat 1314] }

theorem run_fallback_push (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated fallbackPushLocated
      (branchState input 5358) = some (fallbackMidState input) := by
  have hpc : (branchState input 5358).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2224 := by
    simp [branchState, initialState, guardPC0,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  unfold Challenge.EvmProof.Stepper.runLocated
  rw [fallbackPush_index, fallbackPush_instruction, if_pos hpc]
  have hcap : (branchState input 5358).stack.length < 1024 := by
    change [].length < 1024
    decide
  have hwidth : ¬ (2 : Fin 33).val = 0 := by decide
  have hthree : (2 : Fin 33).val + 1 = 3 := by decide
  have hadd : UInt256.ofNat 5358 + UInt256.ofNat 3 = UInt256.ofNat 5361 :=
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
      Artifact.submissionArtifact.instructionPC 2225 := by
    simp [fallbackMidState, initialState, guardPC1,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hcap : (fallbackMidState input).stack.length < 1024 := by
    simp [fallbackMidState]
  have hpcTarget : Artifact.submissionArtifact.instructionPC 977 = 1314 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode 1314 = true := by
    have h := Artifact.isValidJumpDest_index 977 (by rfl)
    unfold Artifact.instructionPC at h
    rwa [hpcTarget] at h
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

private theorem runLocatedBlock_single {artifact : Challenge.EvmProof.ProgramArtifact}
    {fork : EvmSemantics.Fork}
    (p : Challenge.EvmProof.Stepper.Located artifact fork) (s t : State)
    (h : Challenge.EvmProof.Stepper.runLocated p s = some t) :
    Challenge.EvmProof.Stepper.runLocatedBlock [p] s = some t := by
  simp [Challenge.EvmProof.Stepper.runLocatedBlock, h]

theorem run_fallback (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock fallbackPath (branchState input 5358) =
      some (fallbackState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_append [fallbackPushLocated] [fallbackJumpLocated]
    (branchState input 5358) (fallbackMidState input) (fallbackState input)
    (runLocatedBlock_single _ _ _ (run_fallback_push input)) rfl
    (runLocatedBlock_single _ _ _ (run_fallback_jump input))

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Fallback
