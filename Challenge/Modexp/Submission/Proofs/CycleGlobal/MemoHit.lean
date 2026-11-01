import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.MemoRun
import Challenge.Modexp.Submission.Proofs.Bytecode.MemoCert

noncomputable section
set_option warningAsError true
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

/-!
# The answer block of the fixed-vector memo

The recognised tuple pins every byte the specification reads, so its result is the
constant `MemoCert.answer = 3^65535 mod 2^255`.  The hit exit at pc 733 jumps to a
landing pad at pc 60 (formerly an unreachable filler between the Fermat route and the
general-width entry) that pushes the precomputed word and returns it.  No `EXP` is
executed any more.
-/

namespace CycleSubmission.Global.Memo
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM
open CycleSubmission.Global.Dispatch

/-- The answer block's landing pad at pc 60. -/
theorem jumpDestAnswer :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 60 = true :=
  CycleSubmission.Global.Binding.jumpDest 41 (by rfl)

/-- After the jump: the landing pad at pc 60 with an empty stack. -/
def answerEntryState (input : ByteArray) : State := Main.trampolineState input 60

set_option linter.unusedSimpArgs false in
theorem run_hitPre (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hitPrePath (hitEntryState input) =
      some (answerEntryState input) := by
  simp only [hitEntryState, answerEntryState, Main.trampolineState]
  generalize htemplate : initialState CycleSubmission.Artifact.bytecode input 0 = template
  have hcode : template.executionEnv.code = CycleSubmission.Artifact.bytecode := by rw [← htemplate]; rfl
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  have hstack : template.stack = [] := by rw [← htemplate]; rfl
  have hj : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode
      (60 : UInt256).toNat = true := jumpDestAnswer
  have hpc60 : (60 : UInt256) = UInt256.ofNat 60 := rfl
  simp [hitPrePath, opAt, pushAt, hcode, hrun, hstack, hj, hpc60,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  all_goals first | decide | (cases template; simp_all)

def gasSteps_hitPre (input : ByteArray) :
    Challenge.EvmProof.GasSteps (hitEntryState input) (answerEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka hitPrePath rfl rfl
      (run_hitPre input) rfl deployAddress_not_precompile

/-- The answer word the block returns: the `PUSH32` literal, `MemoCert.answer`. -/
def answerWord : UInt256 :=
  26689440342447178617115869845918039756797228267049433585260346420242739014315

/-- After the landing pad, `PUSH32 answer` and `PUSH0`, before the `MSTORE`. -/
def hitPushState (input : ByteArray) : State :=
  { answerEntryState input with
    pc := UInt256.ofNat 95
    stack := [(⟨0⟩ : UInt256), answerWord] }

/-- After the `MSTORE`. -/
def hitStoreState (input : ByteArray) : State :=
  { hitPushState input with
    pc := UInt256.ofNat 96
    stack := []
    memory := MachineState.writeBytes (hitPushState input).memory
      (Data.Bytes.natToBytesPadded answerWord.toNat 32) 0
    activeWords := (hitPushState input).activeWordsAfterUInt256 0 32 }

/-- After `PUSH2 32` and `PUSH0`, at the `RETURN`. -/
def hitReturnArgState (input : ByteArray) : State :=
  { hitStoreState input with
    pc := UInt256.ofNat 100
    stack := [(⟨0⟩ : UInt256), (32 : UInt256)] }

/-- The halted state the block returns from. -/
def hitFinalState (input : ByteArray) : State :=
  { hitReturnArgState input with
    halt := .Returned
    hReturn := MachineState.readPadded (hitReturnArgState input).memory 0 32
    stack := []
    activeWords := (hitReturnArgState input).activeWordsAfterUInt256 0 32 }

set_option linter.unusedSimpArgs false in
theorem run_hitPost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hitPostPath (answerEntryState input) =
      some (hitFinalState input) := by
  simp only [hitFinalState, hitReturnArgState, hitStoreState, hitPushState,
    answerWord, answerEntryState, Main.trampolineState]
  generalize htemplate : initialState CycleSubmission.Artifact.bytecode input 0 = template
  have hcode : template.executionEnv.code = CycleSubmission.Artifact.bytecode := by rw [← htemplate]; rfl
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
    Challenge.EvmProof.GasSteps (answerEntryState input) (hitFinalState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka hitPostPath rfl rfl
      (run_hitPost input) rfl deployAddress_not_precompile

theorem answerWord_toNat : answerWord.toNat = MemoCert.answer := rfl

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
  simp only [hitReturnArgState, hitStoreState]
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

end CycleSubmission.Global.Memo
