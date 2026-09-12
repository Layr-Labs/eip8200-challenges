import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheModel
import Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollBindings

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option warningAsError false
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftDispatchTrace
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

theorem jump_cell (i : Nat) (hi : i < 4) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat (3684 + 39 * i)).toNat = true := by
  interval_cases i
  · exact ShiftUnrollBindings.jump3684
  · exact ShiftUnrollBindings.jump3723
  · exact ShiftUnrollBindings.jump3762
  · exact ShiftUnrollBindings.jump3801

theorem run_dispatch (s : State) (um : ByteArray) (q : UInt256)
    (n bsize esize msize k : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcache : MachineState.readWord um 6304 = ShiftCacheModel.entryWord n)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions ShiftUnrollBindings.dispatchProgram
      (Shift.macDispatchState s um q n bsize esize msize k) =
      some (Shift.macLoopState s um q n bsize esize msize k 0) := by
  have haw : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6304 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have he := ShiftUnrollEntry.entryWord_eq n hn hn32
  have hjump := jump_cell (ShiftUnrollEntry.cellIndex n 0) (ShiftUnrollEntry.index_lt n 0)
  simp (config := { maxSteps := 300000 })
    [runInstructions, ShiftUnrollBindings.dispatchProgram,
     Shift.macDispatchState, Shift.macLoopState, Shift.pcMacLoop,
     Shift.outer, Exp.outer, Monpro.l1Step,
     Challenge.EvmProof.Stepper.runInstr, haw, State.activeWordsAfterUInt256,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod, hcache, he, hcode, hjump]
  have hpow : (2 ^ 256 : Nat) =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num
  simpa only [Challenge.EvmProof.Word.word_toNat_ofNat, hpow] using hjump

#print axioms run_dispatch
end Challenge.Modexp.Submission.Proofs.Fast.ShiftDispatchTrace
