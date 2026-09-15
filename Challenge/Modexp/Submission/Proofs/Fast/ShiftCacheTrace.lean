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

/-- The E5 store.  `n ≤ 8` is needed and not decorative: the block compares `n` to 4 with `EQ`
on the machine word, so without a bound on `n` the claim is false at `n = 4 + 2 ^ 256`.  Every
caller has it (`gasSteps_prologue`'s `hn32`). -/
theorem run_cache (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 88 ≤ s.activeWords.toNat) (hn8 : n ≤ 8) :
    runInstructions ShiftUnrollBindings.cacheProgram (cacheState s mem n bsize esize msize) =
      some (Shift.kState s (ShiftCacheModel.cacheMem mem n) 2546 n n bsize esize msize) := by
  have haw : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1698 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  -- `entryWord` is now a two-way choice on `n`, so the nine reachable limb counts are taken
  -- one at a time: in each branch `EQ` is a comparison of two literals and `entryWord` reduces.
  interval_cases n <;>
    simp (config := { maxSteps := 300000 })
      [runInstructions, ShiftUnrollBindings.cacheProgram, cacheState, Shift.cacheSetupState,
       Shift.kState, Shift.shiftLoopState, Shift.pcShiftLoop, Shift.outer, Exp.outer,
       ShiftCacheModel.cacheMem, ShiftCacheModel.entryWord, Exp.storeWord,
       Challenge.EvmProof.Stepper.runInstr, haw, State.activeWordsAfterUInt256,
       Challenge.EvmProof.Word.literal_eq_ofNat,
       Challenge.EvmProof.Word.word_toNat_ofNat,
       Challenge.EvmProof.Word.succ_ofNat_mod,
       Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange] <;>
    rfl

#print axioms run_cache
end Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheTrace
