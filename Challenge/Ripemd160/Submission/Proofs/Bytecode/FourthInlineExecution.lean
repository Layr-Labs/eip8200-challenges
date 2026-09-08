import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCaps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantGroup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineExecution

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundTemplate CavityQuadGroup
open CachedMaskQuadGroup CachedMaskParams CachedMaskCaps CachedMaskCavitySites

noncomputable def left4_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, (CallsConstantParams.left4 k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s CallsConstantSites.left4.startPC w (mask :: rho))
      (stateAt s CallsConstantSites.left4.endPC
        (CallsConstantGroup.cachedFourResult CallsConstantParams.left4 s w)
        (mask :: rho)) := by
  have hwhole := CallsConstantGroup.run_left_cached_four
    CallsConstantParams.left4 2 (CallsConstantParams.left4 0).constant s
    CallsConstantSites.left4.startPC w rho
    (fun k => CallsConstantParams.left4_function k)
    (fun k => CallsConstantParams.left4_constant k) hfit hstack hrun
  have hsite_end : CallsConstantSites.left4.endPC =
      pcAfter CallsConstantSites.left4.startPC
        (CallsConstantGroup.cachedFourCode CallsConstantParams.left4 2
          (CallsConstantParams.left4 0).constant 0) := by
    simpa only [CallsConstantParams.left4Code] using
      (CavityFragmentChain.site_end CallsConstantSites.left4)
  rw [← hsite_end] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka CallsConstantSites.left4.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw CallsConstantSites.left4
      CallsConstantSites.left4_advances
      (stateAt s CallsConstantSites.left4.startPC w (mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp

noncomputable abbrev left4_group := left4_core

#print axioms left4_core
#print axioms left4_group

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineExecution
