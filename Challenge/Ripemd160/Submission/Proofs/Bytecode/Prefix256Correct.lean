import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Scan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Correct

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

theorem scanAcc_zero_iff_eq (input : ByteArray) (hsize : input.size = 376) :
    scanAcc input 12 = 0 ↔ input = Prefix256Data.data := by
  rw [scanAcc_eq_guardedAcc_376 input hsize 12 (by omega)]
  exact TailProjectionInstances.acc376_zero_iff input hsize

def gasSteps_hit (input : ByteArray) (hsize : input.size = 376)
    (href : KnownInputCompactState.referenceWord input ≠ KnownInputData.fullWord)
    (hz : scanAcc input 12 = 0) :
    GasSteps (initialState submissionBytecode input 0)
      (Prefix256Finish.returnedState input) :=
  (Prefix256Entry.gasSteps_hit input hsize href).trans
    ((Prefix256Scan.gasSteps_scan input hsize).trans
      (Prefix256Finish.gasSteps_finish_hit input (UInt256.ofNat (scalarAt 12))
        384 (scanAcc input 12) hz hsize))

def gasSteps_miss (input : ByteArray) (hsize : input.size = 376)
    (href : KnownInputCompactState.referenceWord input ≠ KnownInputData.fullWord)
    (hne : scanAcc input 12 ≠ 0) :
    GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 368) :=
  (Prefix256Entry.gasSteps_hit input hsize href).trans
    ((Prefix256Scan.gasSteps_scan input hsize).trans
      (Prefix256Finish.gasSteps_miss input (UInt256.ofNat (scalarAt 12))
        384 (scanAcc input 12) hne))

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 376)
    (href : KnownInputCompactState.referenceWord input ≠ KnownInputData.fullWord) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 12 = 0
  · have heq := (scanAcc_zero_iff_eq input hsize).1 hz
    have hspec : spec input = Prefix256Finish.paddedDigest := by
      rw [heq, Prefix256Digest.spec_data_eq]
      rfl
    let trace := gasSteps_hit input hsize href hz
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, Prefix256Finish.returnedState, DigestReturn.returnedState, DigestReturn.storedState,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded Prefix256Finish.answerMemory 0 32)) at heval
    rw [Prefix256Finish.answerMemory_read, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit (gasSteps_miss input hsize href hz)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Correct
