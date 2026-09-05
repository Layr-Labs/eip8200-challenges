import Challenge.Ripemd160.Submission.H39Memo.A1000Loop
import Challenge.Ripemd160.Submission.H39Memo.A1000Recognition

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem guard_cases (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hsize : bytes.size = 1000)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    Trace (entry s) (pattern s) ∨
      Trace (entry s) (fallback s) ∨
        (bytes = inputA1000 ∧ Trace (entry s) (answerEntry s)) := by
  by_cases hfirst : MachineState.readWord bytes 0 = cacheWord
  · have hcache : Trace (entry s) (cached s) :=
      ⟨firstPath, run_first_match s bytes hinput hrun hfirst⟩
    have hloop : Trace (entry s) (loop s 0) :=
      hcache.trans hrun ⟨cachePath, run_cache s hrun⟩
    rcases loop_cases s bytes hinput hrun hcode with hfail | ⟨htail, hwords⟩
    · exact Or.inr (Or.inl (hloop.trans hrun hfail))
    · have htotail := hloop.trans hrun htail
      by_cases hlast : MachineState.readWord bytes 992 = tailWord
      · exact Or.inr (Or.inr
          ⟨input_eq_of_checks bytes hsize hfirst hwords hlast,
            htotail.trans hrun ⟨tailPath, run_tail_match s bytes hinput hrun hlast⟩⟩)
      · exact Or.inr (Or.inl (htotail.trans hrun
          ⟨tailPath, run_tail_mismatch s bytes hinput hrun hlast hcode⟩))
  · have hnotA : Trace (entry s) (notAEntry s) :=
      ⟨firstPath, run_first_mismatch s bytes hinput hrun hfirst hcode⟩
    exact Or.inl (hnotA.trans hrun ⟨notAPath, run_notA s hrun hcode⟩)

theorem Trace.toGasSteps {s t : State} (htrace : Trace s t)
    (hcode : s.executionEnv.code = h39Bytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s t) := by
  obtain ⟨path, hpath⟩ := htrace
  exact ⟨Stepper.runLocatedBlock_sound Artifact.h39Artifact .Osaka path
    (hcode.trans artifact_code.symm) hfork hpath hrun hnp⟩

theorem gasSteps_guard_cases (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hsize : bytes.size = 1000)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps (entry s) (pattern s)) ∨
      Nonempty (GasSteps (entry s) (fallback s)) ∨
        (bytes = inputA1000 ∧ Nonempty (GasSteps (entry s) (answerEntry s))) := by
  rcases guard_cases s bytes hinput hsize hrun hcode with hp | hf | ⟨heq, ha⟩
  · exact Or.inl (hp.toGasSteps hcode hfork hrun hnp)
  · exact Or.inr (Or.inl (hf.toGasSteps hcode hfork hrun hnp))
  · exact Or.inr (Or.inr ⟨heq, ha.toGasSteps hcode hfork hrun hnp⟩)

end Challenge.Ripemd160.Submission.H39Memo.A1000
