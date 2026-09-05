import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

private def tramp0MidState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 3
      stack := [UInt256.ofNat 3133] }

theorem run_tramp0_push (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated tramp0PushLocated
      (initialState submissionBytecode input 0) = some (tramp0MidState input) := by
  have hpc : (initialState submissionBytecode input 0).pc.toNat =
      Artifact.submissionArtifact.instructionPC 0 := by rfl
  unfold Challenge.EvmProof.Stepper.runLocated
  change (if (initialState submissionBytecode input 0).pc.toNat =
      Artifact.submissionArtifact.instructionPC 0 then
      Challenge.EvmProof.Stepper.runInstr (.push 2 (UInt256.ofNat 3133))
        (initialState submissionBytecode input 0) else none) = _
  rw [if_pos hpc]
  have hcap : (initialState submissionBytecode input 0).stack.length < 1024 := by
    change [].length < 1024
    decide
  have hwidth : ¬ (2 : Fin 33).val = 0 := by decide
  have hthree : (2 : Fin 33).val + 1 = 3 := by decide
  have hadd : UInt256.ofNat 0 + UInt256.ofNat 3 = UInt256.ofNat 3 :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos hcap]
  simp only
  rw [if_neg hwidth]
  simp only [tramp0MidState, hthree]
  rw [show (initialState submissionBytecode input 0).pc = UInt256.ofNat 0 by rfl,
    show (initialState submissionBytecode input 0).stack = [] by rfl, hadd]

theorem run_tramp0_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated tramp0JumpLocated
      (tramp0MidState input) = some (trampolineState input 3133) := by
  have hpc : (tramp0MidState input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 1 := by
    simp [tramp0MidState, initialState,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hcap : (tramp0MidState input).stack.length < 1024 := by
    simp [tramp0MidState]
  have hjump : Decode.isValidJumpDest submissionBytecode 3133 = true :=
    Artifact.isValidJumpDest_index 1913 (by rfl)
  unfold Challenge.EvmProof.Stepper.runLocated
  change (if (tramp0MidState input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 1 then
      Challenge.EvmProof.Stepper.runInstr (.op .JUMP) (tramp0MidState input)
      else none) = _
  rw [if_pos hpc]
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos hcap]
  simp only [tramp0MidState]
  rw [show (UInt256.ofNat 3133).toNat = 3133 by decide,
    show (initialState submissionBytecode input 0).executionEnv.code =
      submissionBytecode by rfl, hjump]
  simp only [if_true, trampolineState]
  rw [show (initialState submissionBytecode input 0).stack = [] by rfl]

theorem run_tramp0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState submissionBytecode input 0) = some (trampolineState input 3133) := by
  unfold tramp0Path Challenge.EvmProof.Stepper.runLocatedBlock
  rw [run_tramp0_push]
  change (match (tramp0MidState input).halt with
    | .Running => Challenge.EvmProof.Stepper.runLocatedBlock
        [tramp0JumpLocated] (tramp0MidState input)
    | _ => none) = _
  rw [show (tramp0MidState input).halt = .Running by rfl]
  unfold Challenge.EvmProof.Stepper.runLocatedBlock
  rw [run_tramp0_jump]

set_option linter.unusedSimpArgs false in
theorem run_tramp1 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp1Path
      (trampolineState input 14) = some (trampolineState input 53) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 14) (by norm_num : 14 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 15) (b := 3) (by norm_num : 15 + 3 < 2 ^ 256)
  have hdest : (53 : UInt256).toNat = 53 := by decide
  simp [tramp1Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp2 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp2Path
      (trampolineState input 53) = some (trampolineState input 99) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 53) (by norm_num : 53 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 54) (b := 3) (by norm_num : 54 + 3 < 2 ^ 256)
  have hdest : (99 : UInt256).toNat = 99 := by decide
  simp [tramp2Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp3 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp3Path
      (trampolineState input 99) = some (trampolineState input 305) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 99) (by norm_num : 99 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 100) (b := 3) (by norm_num : 100 + 3 < 2 ^ 256)
  have hdest : (305 : UInt256).toNat = 305 := by decide
  simp [tramp3Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp4 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp4Path
      (trampolineState input 305) = some (trampolineState input 434) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 305) (by norm_num : 305 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 306) (b := 3) (by norm_num : 306 + 3 < 2 ^ 256)
  have hdest : (434 : UInt256).toNat = 434 := by decide
  simp [tramp4Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp5 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp5Path
      (trampolineState input 434) = some (trampolineState input 512) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 434) (by norm_num : 434 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 435) (b := 3) (by norm_num : 435 + 3 < 2 ^ 256)
  have hdest : (512 : UInt256).toNat = 512 := by decide
  simp [tramp5Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp6 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp6Path
      (trampolineState input 512) = some (trampolineState input 699) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 512) (by norm_num : 512 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 513) (b := 3) (by norm_num : 513 + 3 < 2 ^ 256)
  have hdest : (699 : UInt256).toNat = 699 := by decide
  simp [tramp6Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
