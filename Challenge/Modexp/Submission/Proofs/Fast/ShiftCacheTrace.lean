import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheModel
import Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollBindings

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option warningAsError false
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheTrace
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

abbrev cacheState := Shift.cacheSetupState

theorem run_cache (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions ShiftUnrollBindings.cacheProgram (cacheState s mem n bsize esize msize) =
      some (Shift.shiftLoopState s (ShiftCacheModel.cacheMem mem n) n bsize esize msize n) := by
  have haw : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6304 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 300000 })
    [runInstructions, ShiftUnrollBindings.cacheProgram, cacheState, Shift.cacheSetupState,
     Shift.kState, Shift.shiftLoopState, Shift.pcShiftLoop, Shift.outer, Exp.outer,
     ShiftCacheModel.cacheMem, ShiftCacheModel.entryWord, ShiftUnrollEntry.entryWord, Exp.storeWord,
     Challenge.EvmProof.Stepper.runInstr, haw, State.activeWordsAfterUInt256,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]
  have hmask : (UInt256.ofNat 3).land ((⟨0⟩ : UInt256) - UInt256.ofNat n) =
      (UInt256.ofNat 0 - UInt256.ofNat n).land (UInt256.ofNat 3) := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_land]
    exact Nat.and_comm _ _
  rw [hmask]

#print axioms run_cache
end Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheTrace
