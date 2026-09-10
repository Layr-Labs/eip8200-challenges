import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Scan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Logic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Correct

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

theorem correct_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 4 = 0
  · have heq := (Patterned128Logic.scanAcc_zero_iff_eq input hsize).1 hz
    have hspec : spec input = Patterned128Digest.paddedDigest := by
      rw [heq]
      exact Patterned128Digest.spec_data_eq
    let trace := hentry.trans
      ((Patterned128Scan.gasSteps_scan input hsize).trans
        (Patterned128Finish.gasSteps_finish_hit input (UInt256.ofNat (scalarAt 4))
          128 (scanAcc input 4) hz hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, Patterned128Finish.returnedState,
        Patterned128Finish.storedState, Patterned128Finish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded Patterned128Finish.answerMemory 0 32)) at heval
    have hdigest : Patterned128Finish.paddedDigest = Patterned128Digest.paddedDigest := rfl
    rw [Patterned128Finish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((Patterned128Scan.gasSteps_scan input hsize).trans
          (Patterned128Finish.gasSteps_miss input (UInt256.ofNat (scalarAt 4))
            128 (scanAcc input 4) hz)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Correct
