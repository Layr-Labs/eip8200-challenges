import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest32
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest31
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest55
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest119
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest64
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest65
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest128
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierLogic

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternCorrect
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

theorem correct1_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 1) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 1 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq_short input 1 hsize (by decide)).1 hz
    have hspec : spec input = ScanDigest1.paddedDigest := by
      rw [heq]
      exact ScanDigest1.spec_pattern
    let trace := hentry.trans
      (VerifierCorrect.gasSteps_verify_hit 1 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 1) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 1 = ScanDigest1.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        (VerifierCorrect.gasSteps_verify_miss 1 input (by decide) hsize hz))


theorem correct31_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 31) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 31 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq_short input 31 hsize (by decide)).1 hz
    have hspec : spec input = ScanDigest31.paddedDigest := by
      rw [heq]
      exact ScanDigest31.spec_pattern
    let trace := hentry.trans
      (VerifierCorrect.gasSteps_verify_hit 31 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 31) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 31 = ScanDigest31.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        (VerifierCorrect.gasSteps_verify_miss 31 input (by decide) hsize hz))


theorem correct32_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 32) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 32 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq input 32 hsize (by decide)).1 hz
    have hspec : spec input = ScanDigest32.paddedDigest := by
      rw [heq]
      exact ScanDigest32.spec_pattern
    let trace := hentry.trans
      (VerifierCorrect.gasSteps_verify_hit 32 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 32) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 32 = ScanDigest32.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        (VerifierCorrect.gasSteps_verify_miss 32 input (by decide) hsize hz))


theorem correct55_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 55) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 55 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq input 55 hsize (by decide)).1 hz
    have hspec : spec input = ScanDigest55.paddedDigest := by
      rw [heq]
      exact ScanDigest55.spec_pattern
    let trace := hentry.trans
      (VerifierCorrect.gasSteps_verify_hit 55 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 55) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 55 = ScanDigest55.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        (VerifierCorrect.gasSteps_verify_miss 55 input (by decide) hsize hz))


theorem correct56_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 56 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq input 56 hsize (by decide)).1 hz
    have hspec : spec input = ShortPatternDigest.paddedDigest56 := by
      rw [heq]
      exact ShortPatternDigest.spec_pattern56
    let trace := hentry.trans
      (VerifierCorrect.gasSteps_verify_hit 56 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 56) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 56 = ShortPatternDigest.paddedDigest56 := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        (VerifierCorrect.gasSteps_verify_miss 56 input (by decide) hsize hz))


theorem correct120_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 120) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 120 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq input 120 hsize (by decide)).1 hz
    have hspec : spec input = ShortPatternDigest.paddedDigest120 := by
      rw [heq]
      exact ShortPatternDigest.spec_pattern120
    let trace := hentry.trans
      (VerifierCorrect.gasSteps_verify_hit 120 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 120) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 120 = ShortPatternDigest.paddedDigest120 := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        (VerifierCorrect.gasSteps_verify_miss 120 input (by decide) hsize hz))


theorem correct119_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 119) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 119 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq input 119 hsize (by decide)).1 hz
    have hspec : spec input = ScanDigest119.paddedDigest := by
      rw [heq]
      exact ScanDigest119.spec_pattern
    let trace := hentry.trans
      (VerifierCorrect.gasSteps_verify_hit 119 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 119) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 119 = ScanDigest119.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        (VerifierCorrect.gasSteps_verify_miss 119 input (by decide) hsize hz))


theorem correct64_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 64) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 64 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq input 64 hsize (by decide)).1 hz
    have hspec : spec input = ScanDigest64.paddedDigest := by
      rw [heq]
      exact ScanDigest64.spec_pattern
    let trace := hentry.trans
      (VerifierCorrect.gasSteps_verify_hit 64 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 64) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 64 = ScanDigest64.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        (VerifierCorrect.gasSteps_verify_miss 64 input (by decide) hsize hz))


theorem correct65_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 65) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 65 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq input 65 hsize (by decide)).1 hz
    have hspec : spec input = ScanDigest65.paddedDigest := by
      rw [heq]
      exact ScanDigest65.spec_pattern
    let trace := hentry.trans
      (VerifierCorrect.gasSteps_verify_hit 65 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 65) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 65 = ScanDigest65.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        (VerifierCorrect.gasSteps_verify_miss 65 input (by decide) hsize hz))


theorem correct128_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128) (_hbyte : DirectGuard.firstByte input = 7)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 128 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq input 128 hsize (by decide)).1 hz
    have hspec : spec input = ScanDigest128.paddedDigest := by
      rw [heq]
      exact ScanDigest128.spec_pattern
    let trace := hentry.trans
      (VerifierCorrect.gasSteps_verify_hit 128 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 128) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 128 = ScanDigest128.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        (VerifierCorrect.gasSteps_verify_miss 128 input (by decide) hsize hz))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternCorrect
