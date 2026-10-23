import Challenge.Modexp.Submission.Proofs.Bytecode.MemoRun
import Challenge.Modexp.Submission.Proofs.Bytecode.MemoCert

set_option warningAsError true
set_option maxRecDepth 400000
set_option maxHeartbeats 8000000


namespace Challenge.Modexp.Submission.Proofs.Bytecode.Memo

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

def landedState (input : ByteArray) : State :=
  { Main.trampolineState input 8616 with
    stack := [] }

set_option linter.unusedSimpArgs false in
theorem run_hitPre (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hitPrePath (hitEntryState input) =
      some (landedState input) := by
  simp only [hitEntryState, landedState, Main.trampolineState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hcode : template.executionEnv.code = submissionBytecode := by rw [← htemplate]; rfl
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  have hstack : template.stack = [] := by rw [← htemplate]; rfl
  have hpc : Artifact.instructionPC 6727 = 8616 := by rfl
  have hjd : Decode.isValidJumpDest template.executionEnv.code 8616 = true := by
    rw [hcode, ← hpc]
    exact Artifact.isValidJumpDest_index 6727 (by rfl)
  simp [hitPrePath, opAt, pushAt, hcode, hrun, hstack, hjd,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  all_goals decide

def gasSteps_hitPre (input : ByteArray) :
    Challenge.EvmProof.GasSteps (hitEntryState input) (landedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka hitPrePath rfl rfl
      (run_hitPre input) rfl deployAddress_not_precompile

def answerWord : UInt256 :=
  UInt256.ofNat 0x3b01b01ac41f2d6e917c6d6a221ce793802469026d9ab7578fa2e79e4da6aaab

def hitDestState (input : ByteArray) : State :=
  { landedState input with
    pc := (landedState input).pc.succ }

def hitWordState (input : ByteArray) : State :=
  { hitDestState input with
    pc := (hitDestState input).pc + UInt256.ofNat 33
    stack := [answerWord] }

/-- After `PUSH0`, before the `MSTORE`. -/
def hitPushState (input : ByteArray) : State :=
  { hitWordState input with
    pc := (hitWordState input).pc.succ
    stack := (⟨0⟩ : UInt256) :: (hitWordState input).stack }

/-- After the `MSTORE`. -/
def hitStoreState (input : ByteArray) : State :=
  { hitPushState input with
    pc := (hitPushState input).pc.succ
    stack := []
    memory := MachineState.writeBytes (hitPushState input).memory
      (Data.Bytes.natToBytesPadded answerWord.toNat 32) 0
    activeWords := (hitPushState input).activeWordsAfterUInt256 0 32 }

/-- After `PUSH1 32`. -/
def hitSizeState (input : ByteArray) : State :=
  { hitStoreState input with
    pc := (hitStoreState input).pc.succ.succ
    stack := [(32 : UInt256)] }

/-- After the second `PUSH0`. -/
def hitReturnArgState (input : ByteArray) : State :=
  { hitSizeState input with
    pc := (hitSizeState input).pc.succ
    stack := (⟨0⟩ : UInt256) :: (hitSizeState input).stack }

/-- The halted state the block returns from. -/
def hitFinalState (input : ByteArray) : State :=
  { hitReturnArgState input with
    halt := .Returned
    hReturn := MachineState.readPadded (hitReturnArgState input).memory 0 32
    stack := []
    activeWords := (hitReturnArgState input).activeWordsAfterUInt256 0 32 }

set_option linter.unusedSimpArgs false in
theorem run_hitPost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hitPostPath (landedState input) =
      some (hitFinalState input) := by
  simp only [hitFinalState, hitReturnArgState, hitSizeState, hitStoreState, hitPushState,
    hitWordState, hitDestState, answerWord, landedState, Main.trampolineState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hcode : template.executionEnv.code = submissionBytecode := by rw [← htemplate]; rfl
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have hstack : template.stack = [] := by rw [← htemplate]; rfl
  simp [hitPostPath, opAt, pushAt, hcode, hrun, hstack, hzero, h32,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  all_goals decide

def gasSteps_hitPost (input : ByteArray) :
    Challenge.EvmProof.GasSteps (landedState input) (hitFinalState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka hitPostPath rfl rfl
      (run_hitPost input) rfl deployAddress_not_precompile

theorem answerWord_toNat : answerWord.toNat = MemoCert.answer := by
  simp only [answerWord, MemoCert.answer, Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num

theorem hitFinalState_isDone (input : ByteArray) :
    (hitFinalState input).isDone = true := rfl

theorem hitFinalState_result (input : ByteArray) (hvalid : ValidInput input)
    (hmatch : MemoLogic.Matches input) :
    (hitFinalState input).toResult = .returned (Challenge.Modexp.spec input) := by
  rw [MemoCert.spec_eq input hvalid hmatch]
  have hsize : (Data.Bytes.natToBytesPadded answerWord.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  have hread := Challenge.EvmProof.Memory.readPadded_writeBytes_same
    (hitPushState input).memory (Data.Bytes.natToBytesPadded answerWord.toNat 32) 0
  rw [hsize] at hread
  show ExecutionResult.returned
      (MachineState.readPadded (hitReturnArgState input).memory 0 32) = _
  simp only [hitReturnArgState, hitSizeState, hitStoreState]
  rw [hread, answerWord_toNat]
  rfl

/-- The answer block returns the specified result for every recognised input. -/
theorem hitHandled (input : ByteArray) (hvalid : ValidInput input)
    (hmatch : MemoLogic.Matches input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps (entryState input) final) ∧
        final.isDone = true ∧ final.toResult = .returned (Challenge.Modexp.spec input) :=
  ⟨hitFinalState input,
    ⟨(gasSteps_hit input hmatch).trans
      ((gasSteps_hitPre input).trans (gasSteps_hitPost input))⟩,
    hitFinalState_isDone input, hitFinalState_result input hvalid hmatch⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
