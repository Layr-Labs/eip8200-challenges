import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Scan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Correct

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

theorem scanAcc_zero_iff_eq (input : ByteArray) (hsize : input.size = 128) :
    scanAcc input 4 = 0 ↔ input = Prefix128Data.data := by
  rw [scanAcc_zero_iff]
  constructor
  · intro hw
    apply Prefix128Data.eq_data_of_words input hsize
    intro j hj
    rw [hw j hj, guardWord_eq j (by omega)]
  · rintro rfl j hj
    rw [Prefix128Data.readWord_data j hj, guardWord_eq j (by omega)]

def gasSteps_hit (input : ByteArray) (hsize : input.size = 128)
    (hz : scanAcc input 4 = 0) (h7 : PatternedScanGate.firstByte input = 7) :
    GasSteps (initialState submissionBytecode input 0)
      (Prefix128Finish.returnedState input) :=
  (Prefix256Entry.gasSteps_hit128 input hsize).trans
    ((Prefix128Scan.gasSteps_scan input hsize h7).trans
      (Prefix128Finish.gasSteps_finish_hit input (UInt256.ofNat (scalarAt 4))
        128 (scanAcc input 4) hsize hz))

def gasSteps_miss (input : ByteArray) (hsize : input.size = 128)
    (hne : scanAcc input 4 ≠ 0) (h7 : PatternedScanGate.firstByte input = 7) :
    GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 0x16c) :=
  (Prefix256Entry.gasSteps_hit128 input hsize).trans
    ((Prefix128Scan.gasSteps_scan input hsize h7).trans
      (Prefix256Finish.gasSteps_miss input (UInt256.ofNat (scalarAt 4))
        128 (scanAcc input 4) hne))

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases h7 : PatternedScanGate.firstByte input = 7
  swap
  · exact StackCorrect.correct input hfit
      ((Prefix256Entry.gasSteps_hit128 input hsize).trans (PatternedScanGate.gasSteps_exit input h7))
  by_cases hz : scanAcc input 4 = 0
  · have heq := (scanAcc_zero_iff_eq input hsize).1 hz
    have hspec : spec input = Prefix128Digest.paddedDigest := by
      rw [heq, Prefix128Digest.spec_data_eq]
    let trace := gasSteps_hit input hsize hz h7
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, Prefix128Finish.returnedState, Prefix128Finish.storedState,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded Prefix128Finish.answerMemory 0 32)) at heval
    rw [Prefix128Finish.answerMemory_read, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit (gasSteps_miss input hsize hz h7)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Correct
