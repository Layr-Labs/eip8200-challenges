import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCaps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineExecution

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundTemplate CavityQuadGroup
open CachedMaskQuadGroup CachedMaskParams CachedMaskCaps CachedMaskCavitySites

noncomputable def left4_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 4) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left4First.startPC w (mask :: rho))
      (stateAt s left4First.endPC (fourResult (left 4) s w) (mask :: rho)) := by
  have hwhole := run_leftCode 4 s left4First.startPC w rho hfit hstack hrun
  rw [← CavityFragmentChain.site_end left4First] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka left4First.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw left4First (left_advances 4)
      (stateAt s left4First.startPC w (mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp

noncomputable abbrev left4_group := left4_core

#print axioms left4_core
#print axioms left4_group

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineExecution
