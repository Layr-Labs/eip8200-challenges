import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan32
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest32
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan31
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest31
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan55
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest55
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan119
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest119
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan64
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest64
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan65
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest65
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan128
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest128
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan56
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan120
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternCorrect
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

theorem correct1_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 1)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 1 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_1 input hsize).1 hz
    have hspec : spec input = ScanDigest1.paddedDigest := by
      rw [heq]
      exact ScanDigest1.spec_pattern
    let trace := hentry.trans
      ((ShortPatternScan1.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 1 input (UInt256.ofNat (scalarAt 1))
          32 (scanAcc input 1) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 1) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 1 = ScanDigest1.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan1.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 1))
            32 (scanAcc input 1) hz)))


theorem correct31_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 31)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 1 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_31 input hsize).1 hz
    have hspec : spec input = ScanDigest31.paddedDigest := by
      rw [heq]
      exact ScanDigest31.spec_pattern
    let trace := hentry.trans
      ((ShortPatternScan31.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 31 input (UInt256.ofNat (scalarAt 1))
          32 (scanAcc input 1) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 31) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 31 = ScanDigest31.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan31.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 1))
            32 (scanAcc input 1) hz)))


theorem correct32_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 32)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 1 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_32 input hsize).1 hz
    have hspec : spec input = ScanDigest32.paddedDigest := by
      rw [heq]
      exact ScanDigest32.spec_pattern
    let trace := hentry.trans
      ((ShortPatternScan32.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 32 input (UInt256.ofNat (scalarAt 1))
          32 (scanAcc input 1) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 32) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 32 = ScanDigest32.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan32.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 1))
            32 (scanAcc input 1) hz)))


theorem correct55_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 55)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 2 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_55 input hsize).1 hz
    have hspec : spec input = ScanDigest55.paddedDigest := by
      rw [heq]
      exact ScanDigest55.spec_pattern
    let trace := hentry.trans
      ((ShortPatternScan55.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 55 input (UInt256.ofNat (scalarAt 2))
          64 (scanAcc input 2) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 55) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 55 = ScanDigest55.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan55.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 2))
            64 (scanAcc input 2) hz)))


theorem correct56_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 2 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_56 input hsize).1 hz
    have hspec : spec input = ShortPatternDigest.paddedDigest56 := by
      rw [heq]
      exact ShortPatternDigest.spec_pattern56
    let trace := hentry.trans
      ((ShortPatternScan56.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 56 input (UInt256.ofNat (scalarAt 2))
          64 (scanAcc input 2) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 56) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 56 = ShortPatternDigest.paddedDigest56 := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan56.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 2))
            64 (scanAcc input 2) hz)))


theorem correct120_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 120)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 4 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_120 input hsize).1 hz
    have hspec : spec input = ShortPatternDigest.paddedDigest120 := by
      rw [heq]
      exact ShortPatternDigest.spec_pattern120
    let trace := hentry.trans
      ((ShortPatternScan120.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 120 input (UInt256.ofNat (scalarAt 4))
          128 (scanAcc input 4) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 120) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 120 = ShortPatternDigest.paddedDigest120 := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan120.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 4))
            128 (scanAcc input 4) hz)))


theorem correct119_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 119)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 4 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_119 input hsize).1 hz
    have hspec : spec input = ScanDigest119.paddedDigest := by
      rw [heq]
      exact ScanDigest119.spec_pattern
    let trace := hentry.trans
      ((ShortPatternScan119.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 119 input (UInt256.ofNat (scalarAt 4))
          128 (scanAcc input 4) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 119) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 119 = ScanDigest119.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan119.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 4))
            128 (scanAcc input 4) hz)))


#print axioms correct56_from_patternedEntry
#print axioms correct120_from_patternedEntry

theorem correct64_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 64)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 2 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_64 input hsize).1 hz
    have hspec : spec input = ScanDigest64.paddedDigest := by
      rw [heq]
      exact ScanDigest64.spec_pattern
    let trace := hentry.trans
      ((ShortPatternScan64.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 64 input (UInt256.ofNat (scalarAt 2))
          64 (scanAcc input 2) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 64) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 64 = ScanDigest64.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan64.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 2))
            64 (scanAcc input 2) hz)))



theorem correct65_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 65)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 3 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_65 input hsize).1 hz
    have hspec : spec input = ScanDigest65.paddedDigest := by
      rw [heq]
      exact ScanDigest65.spec_pattern
    let trace := hentry.trans
      ((ShortPatternScan65.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 65 input (UInt256.ofNat (scalarAt 3))
          96 (scanAcc input 3) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 65) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 65 = ScanDigest65.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan65.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 3))
            96 (scanAcc input 3) hz)))



theorem correct128_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 4 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_128 input hsize).1 hz
    have hspec : spec input = ScanDigest128.paddedDigest := by
      rw [heq]
      exact ScanDigest128.spec_pattern
    let trace := hentry.trans
      ((ShortPatternScan128.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 128 input (UInt256.ofNat (scalarAt 4))
          128 (scanAcc input 4) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 128) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 128 = ScanDigest128.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan128.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 4))
            128 (scanAcc input 4) hz)))



end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternCorrect
