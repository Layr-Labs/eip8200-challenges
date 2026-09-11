import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Scan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Correct

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

theorem scanAcc_zero_iff_eq (input : ByteArray) (hsize : input.size = 256) :
    scanAcc input 8 = 0 ↔ input = Patterned256Data.data := by
  rw [scanAcc_eq_guardedAcc_256 input hsize 8 (by omega)]
  exact TailProjectionInstances.acc256_zero_iff input hsize

def gasSteps_hit (input : ByteArray) (hsize : input.size = 256)
    (href : KnownInputCompactState.referenceWord input ≠ KnownInputData.fullWord)
    (hz : scanAcc input 8 = 0) :
    GasSteps (initialState submissionBytecode input 0)
      (Patterned256Finish.returnedState input) :=
  (Patterned256Entry.gasSteps_hit input hsize href).trans
    ((Patterned256Scan.gasSteps_scan input hsize).trans
      (Patterned256Finish.gasSteps_finish_hit input (UInt256.ofNat (scalarAt 8))
        256 (scanAcc input 8) hz hsize))

def gasSteps_miss (input : ByteArray) (hsize : input.size = 256)
    (href : KnownInputCompactState.referenceWord input ≠ KnownInputData.fullWord)
    (hne : scanAcc input 8 ≠ 0) :
    GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 276) :=
  (Patterned256Entry.gasSteps_hit input hsize href).trans
    ((Patterned256Scan.gasSteps_scan input hsize).trans
      (Patterned256Finish.gasSteps_miss input (UInt256.ofNat (scalarAt 8))
        256 (scanAcc input 8) hne))

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 256)
    (href : KnownInputCompactState.referenceWord input ≠ KnownInputData.fullWord) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 8 = 0
  · have heq := (scanAcc_zero_iff_eq input hsize).1 hz
    have hspec : spec input = Patterned256Finish.paddedDigest := by
      rw [heq, Patterned256Digest.spec_data_eq]
      rfl
    let trace := gasSteps_hit input hsize href hz
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, Patterned256Finish.returnedState, ShortPatternFinish.returnedState, ShortPatternFinish.storedState,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded Patterned256Finish.answerMemory 0 32)) at heval
    rw [Patterned256Finish.answerMemory_read, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit (gasSteps_miss input hsize href hz)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Correct
