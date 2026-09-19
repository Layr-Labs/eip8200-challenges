import Challenge.Modexp.Submission.Proofs.Bytecode.MemoRun
import Challenge.Modexp.Submission.Proofs.Bytecode.MemoCert
import Challenge.Modexp.Submission.Proofs.Bytecode.Exp

set_option warningAsError true
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

/-!
# The answer block of the fixed-vector memo

Three pieces: the two operand pushes, the single `EXP`, and the store-and-return
tail.  `EXP` is the only instruction the shared straight-line evaluator does not
step, so it is taken separately through `Exp.step` and the three are composed.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Memo

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

/-- State after the two operand pushes, at the `EXP`. -/
def expArgState (input : ByteArray) : State :=
  { Main.trampolineState input 836 with
    stack := [UInt256.ofNat 3, UInt256.ofNat 65535] }

set_option linter.unusedSimpArgs false in
theorem run_hitPre (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hitPrePath (hitEntryState input) =
      some (expArgState input) := by
  simp only [hitEntryState, expArgState, Main.trampolineState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hcode : template.executionEnv.code = submissionBytecode := by rw [← htemplate]; rfl
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  have hstack : template.stack = [] := by rw [← htemplate]; rfl
  simp [hitPrePath, opAt, pushAt, hcode, hrun, hstack,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  exact ⟨by decide, by decide⟩

/-- The `EXP` at index 596 decodes from the artifact like any other instruction. -/
theorem exp_decodes (s : State)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hpc : s.pc.toNat = 836) :
    s.decodedOp = some .EXP := by
  have hdec := Challenge.EvmProof.Stepper.decodes_of_artifact
    Artifact.submissionArtifact s 596 (.op .EXP) hcode
    (by rw [hpc]; rfl) (by rfl) expAt.wellFormed
  change s.decodedOp = some .EXP at hdec
  exact hdec

/-- State after the `EXP`. -/
def expDoneState (input : ByteArray) : State :=
  { expArgState input with
    pc := (expArgState input).pc.succ
    stack := [UInt256.exp (UInt256.ofNat 3) (UInt256.ofNat 65535)] }

def gasSteps_hitPre (input : ByteArray) :
    Challenge.EvmProof.GasSteps (hitEntryState input) (expArgState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka hitPrePath rfl rfl
      (run_hitPre input) rfl deployAddress_not_precompile

def gasSteps_exp (input : ByteArray) :
    Challenge.EvmProof.GasSteps (expArgState input) (expDoneState input) :=
  Exp.step (s := expArgState input)
    (exp_decodes (expArgState input) rfl (by rfl))
    (by rfl) (by simp [expArgState]; decide) rfl deployAddress_not_precompile

/-- The answer word the block returns. -/
def answerWord : UInt256 := UInt256.exp (UInt256.ofNat 3) (UInt256.ofNat 65535)

/-- After `PUSH0`, before the `MSTORE`. -/
def hitPushState (input : ByteArray) : State :=
  { expDoneState input with
    pc := (expDoneState input).pc.succ
    stack := (⟨0⟩ : UInt256) :: (expDoneState input).stack }

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
    Challenge.EvmProof.Stepper.runLocatedBlock hitPostPath (expDoneState input) =
      some (hitFinalState input) := by
  simp only [hitFinalState, hitReturnArgState, hitSizeState, hitStoreState, hitPushState,
    answerWord, expDoneState, expArgState, Main.trampolineState]
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

def gasSteps_hitPost (input : ByteArray) :
    Challenge.EvmProof.GasSteps (expDoneState input) (hitFinalState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka hitPostPath rfl rfl
      (run_hitPost input) rfl deployAddress_not_precompile

theorem answerWord_toNat : answerWord.toNat = MemoCert.answer := by
  simp only [answerWord, Exp.exp_three_ffff, Challenge.EvmProof.Word.word_toNat_ofNat,
    MemoCert.answer]
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
      ((gasSteps_hitPre input).trans
        ((gasSteps_exp input).trans (gasSteps_hitPost input)))⟩,
    hitFinalState_isDone input, hitFinalState_result input hvalid hmatch⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
