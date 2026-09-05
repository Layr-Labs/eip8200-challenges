import Challenge.Ripemd160.Submission.H39Memo.PatternTraceResult
import Challenge.Ripemd160.Submission.H39Memo.Digest

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState

theorem Trace.toGasSteps {s t : State} (htrace : Trace s t)
    (hcode : s.executionEnv.code = h39Bytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s t) := by
  obtain ⟨path, hpath⟩ := htrace
  exact ⟨Stepper.runLocatedBlock_sound Artifact.h39Artifact .Osaka path
    hcode hfork hpath hrun hnp⟩

theorem finish (s : State) (bytes : ByteArray) (pc : Nat)
    (ho : Outcome s bytes (stateAt s bytes pc))
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps (stateAt s bytes pc) (fallback s)) ∨
      ∃ t : State, Nonempty (GasSteps (stateAt s bytes pc) t) ∧
        t.halt = .Returned ∧ t.hReturn = spec bytes := by
  rcases ho with hf | ⟨p, heq, hout⟩
  · exact Or.inl (hf.toGasSteps hcode hfork hrun hnp)
  · obtain ⟨g⟩ := hout.toGasSteps hcode hfork hrun hnp
    let i := PatternFacts.targetIndex p
    let out := outputEntry s (TerminalPathsSites.outputPC i)
    let gout := TerminalPathsSites.gasSteps_output i out rfl rfl hrun hcode hfork hnp
    refine Or.inr ⟨returned out (TerminalPathsSites.outputPC i + 26)
      (TerminalPathsSites.digest i), ⟨g.trans gout⟩, rfl, ?_⟩
    rw [TerminalPathsSites.returned_expected, heq]
    exact (digest_correct i).symm

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
