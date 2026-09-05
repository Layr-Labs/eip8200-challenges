import Challenge.Modexp.Submission.Proofs.Memo.Dispatch

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.EmptyReturn

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Dispatch

/-- Appended empty-return block: `JUMPDEST PUSH0 PUSH0 RETURN`. -/
def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1732 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1733 0 0,
   Main.pushAt 1734 0 0,
   Main.opAt 1735 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 4330
      stack := []
      activeWords := UInt256.ofNat 0
      halt := .Returned
      hReturn := MachineState.readPadded ByteArray.empty 0 0 }

theorem run_return (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock returnPath (Main.trampolineState input 4327) =
    some (returnedState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [returnPath, returnedState, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc22,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

/-- A zero modulus-length word forces empty specification output. -/
theorem spec_empty_of_modword (input : ByteArray)
    (h : MachineState.readWord input 64 = UInt256.ofNat 0) :
    Challenge.Modexp.spec input = ByteArray.empty := by
  have hmsize : Challenge.Modexp.modulusSize input = 0 := by
    unfold Challenge.Modexp.modulusSize
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h]
    rfl
  simp [Challenge.Modexp.spec, hmsize]

@[simp] theorem returnedState_isDone (input : ByteArray) :
    (returnedState input).isDone = true := by
  simp [returnedState, State.isDone, State.isHalted, State.isRunning]
  rfl

theorem returnedState_result (input : ByteArray)
    (h : MachineState.readWord input 64 = UInt256.ofNat 0) :
    (returnedState input).toResult = .returned (Challenge.Modexp.spec input) := by
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned (MachineState.readPadded ByteArray.empty 0 0) = _
  rw [show MachineState.readPadded ByteArray.empty 0 0 = ByteArray.empty by decide +kernel,
    spec_empty_of_modword input h]

end Challenge.Modexp.Submission.Proofs.Memo.EmptyReturn
