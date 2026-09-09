import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceLater
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFirst
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-!
# H8 dispatcher composition

This module binds the checked-prefix execution certificates to the nonempty
block dispatcher.  The first certificate handles the CODECOPY and word-0
comparison.  On a word-0 match, the finish certificate handles the word-32
comparison and the H1 stores.  Later blocks use the direct later-path
certificate.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PrefixStateModel PrefixStateMemory PrefixStatePaths

abbrev Hnp (s : State) : Prop :=
  Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

/-- Full nonempty-dispatcher execution certificate.

For block zero this composes the first-word certificate with the finish
certificate (word-1 guard, depth-2 rung, install).  For later blocks it uses
the checked later-path certificate. -/
def gasSteps_dispatch (s : State) (input : ByteArray) (i : Nat)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Hnp s) :
    GasSteps (FastEmptyBlock.nonemptyEntry s input i)
      (if i = 0 ∧ Matched input then
        (if Matched2 input then
          (if Matched3 input then resultState3 (copied s) input else resultState2 (copied s) input)
          else resultState (copied s) input i)
        else DriverTrace.compressEntry (prepared s i) input i) := by
  by_cases hzero : i = 0
  · subst i
    by_cases hw0 : MachineState.readWord input 0 =
        PatternedWordData.expectedWordAt 0
    · have gfirst : GasSteps (FastEmptyBlock.nonemptyEntry s input 0)
          (PrefixStateTraceFirst.firstMatchedState s input) := by
        have g := PrefixStateTraceFirst.gasSteps_first s input
          hcalldata hcode hfork hrun hnp
        rw [if_pos hw0] at g
        exact g
      have hcalldata' : (copied s).executionEnv.calldata = input := by
        simpa using hcalldata
      have hcode' : (copied s).executionEnv.code = submissionBytecode := by
        simpa using hcode
      have hfork' : (copied s).fork = .Osaka := by
        simpa [State.fork] using hfork
      have hrun' : (copied s).halt = .Running := by
        simpa using hrun
      have hnp' : Hnp (copied s) := by
        simpa only [Hnp, copied_executionEnv] using hnp
      have hentry : PrefixStateTraceFinish.entry (copied s) input =
          PrefixStateTraceFirst.firstMatchedState s input := by
        rfl
      have g := PrefixStateTraceFinish.gasSteps_finish (copied s) input
        hcalldata' hcode' hfork' hrun' hnp'
      rw [hentry] at g
      by_cases hw1 : MachineState.readWord input 32 =
          PatternedWordData.expectedWordAt 1
      · rw [if_pos hw1] at g
        have hmatch : Matched input := ⟨hw0, hw1⟩
        rw [if_pos ⟨rfl, hmatch⟩]
        exact gfirst.trans g
      · rw [if_neg hw1] at g
        have hnot : ¬ (0 = 0 ∧ Matched input) := by
          intro h
          exact hw1 h.2.2
        rw [if_neg hnot]
        simpa [PrefixStateModel.prepared] using gfirst.trans g
    · have gfirst : GasSteps (FastEmptyBlock.nonemptyEntry s input 0)
          (DriverTrace.compressEntry (copied s) input 0) := by
        have g := PrefixStateTraceFirst.gasSteps_first s input
          hcalldata hcode hfork hrun hnp
        rw [if_neg hw0] at g
        exact g
      have hnot : ¬ (0 = 0 ∧ Matched input) := by
        intro h
        exact hw0 h.2.1
      rw [if_neg hnot]
      simpa [PrefixStateModel.prepared] using gfirst
  · rw [if_neg (fun h => hzero h.1)]
    exact PrefixStateTraceLater.gasSteps_later_of_bounds s input i hzero
      hfit hi hcode hfork hrun hnp

#print axioms gasSteps_dispatch

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTrace
