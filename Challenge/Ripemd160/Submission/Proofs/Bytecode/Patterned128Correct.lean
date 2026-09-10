import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Scan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Logic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Correct

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    GasSteps (initialState submissionBytecode input 0)
      (Patterned128Finish.returnedState input) :=
  hentry.trans
    ((Patterned128Scan.gasSteps_scan input hsize).trans
      (Patterned128Finish.gasSteps_finish_hit input
        (UInt256.ofNat (scalarAt 4)) 128 (scanAcc input 4) (by rfl) hsize))

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input))
    (hne : scanAcc input 4 ≠ 0) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.fallbackState input) :=
  hentry.trans
    ((Patterned128Scan.gasSteps_scan input hsize).trans
      (Patterned128Finish.gasSteps_miss input
        (UInt256.ofNat (scalarAt 4)) 128 (scanAcc input 4) hne))

theorem correct_from_patternedEntry (input : ByteArray)
    (hfit : CalldataFits input) (hsize : input.size = 128)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 4 = 0
  · have heq := (Patterned128Logic.scanAcc_zero_iff_eq input hsize).1 hz
    have hspec : spec input = Patterned128Finish.paddedDigest := by
      rw [heq, Patterned128Digest.spec_data_eq]
      rfl
    let trace := gasSteps_hit input hfit hsize hentry
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, Patterned128Finish.returnedState, initialState,
        State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded Patterned128Finish.answerMemory 0 32)) at heval
    rw [Patterned128Finish.answerMemory_read, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · have hmiss := gasSteps_miss input hfit hsize hentry hz
    exact StackCorrect.correct input hfit (by
      simpa [PatternedScan.fallbackState, PatternedScan.atPC,
        Execution.atPC] using hmiss)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Correct
