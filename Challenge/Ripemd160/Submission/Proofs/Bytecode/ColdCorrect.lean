import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighPrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Correct
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 600000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdCorrect
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

noncomputable opaque highTrace (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (i : Nat) (hi : i < DriverTrace.blockCount input)
    (hh : input.size = DriverTrace.blockOffset i) (hlarge : 5224 ≤ input.size)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 336)) :
    GasSteps (initialState submissionBytecode input 0) (ColdHighFinish.resultState input i) :=
  ColdTraceCompose.two (ColdHighPrefix.gasSteps input hfit hpositive hn32 i hi hh entryPrefix)
    (ColdTraceCompose.two (ColdHighTrace.gasSteps_setup input hfit hpositive i hi hh hlarge)
      (ColdHighFinish.gasSteps input hfit i hi hh))

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 336)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  classical
  by_cases ho : ∀ i, i < DriverTrace.blockCount input →
      input.size = DriverTrace.blockOffset i → input.size < 5224
  · exact ColdOrdinaryCorrect.correct input hfit hpositive hn32 ho entryPrefix
  · push Not at ho
    obtain ⟨i, hi, hh, hlarge⟩ := ho
    exact Shared32Correct.eval_of_initial_returned input (ColdHighFinish.resultState input i)
      (highTrace input hfit hpositive hn32 i hi hh hlarge entryPrefix)
      (ColdHighFinish.resultState_halt input i) (ColdHighFinish.resultState_callStack input i)
      (ColdHighFinish.returned_spec input hfit hpositive i hi hh)

#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdCorrect
