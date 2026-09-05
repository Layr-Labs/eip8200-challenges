import Challenge.Ripemd160.Submission.H39Memo.A1000Compose
import Challenge.Ripemd160.Submission.H39Memo.A1000Output
import Challenge.Ripemd160.Submission.H39Memo.DigestA1000
import Challenge.Ripemd160.Submission.H39Memo.TerminalPaths

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem answerState_expected (s : State) :
    (answerState s).hReturn = expectedA1000 := by
  rw [answerState, TerminalPaths.returned_hReturn,
    Memory.natToBytesPadded_eq_natToBE]
  decide

theorem correct (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hsize : bytes.size = 1000)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps (entry s) (pattern s)) ∨
      Nonempty (GasSteps (entry s) (fallback s)) ∨
        (bytes = inputA1000 ∧ Nonempty (GasSteps (entry s) (answerState s)) ∧
          (answerState s).halt = .Returned ∧
          (answerState s).hReturn = spec bytes) := by
  rcases guard_cases s bytes hinput hsize hrun hcode with hp | hf | ⟨heq, ha⟩
  · exact Or.inl (hp.toGasSteps hcode hfork hrun hnp)
  · exact Or.inr (Or.inl (hf.toGasSteps hcode hfork hrun hnp))
  · have hreturn : Trace (entry s) (answerState s) :=
      ha.trans hrun ⟨answerPath, run_answer s hrun⟩
    refine Or.inr (Or.inr ⟨heq, hreturn.toGasSteps hcode hfork hrun hnp, rfl, ?_⟩)
    rw [heq, spec_A1000, answerState_expected]

end Challenge.Ripemd160.Submission.H39Memo.A1000
