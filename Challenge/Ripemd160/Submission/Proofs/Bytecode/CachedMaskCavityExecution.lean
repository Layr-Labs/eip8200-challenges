import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCaps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavityExecution

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundTemplate CavityQuadGroup
open CachedMaskQuadGroup CachedMaskParams CachedMaskCaps CachedMaskCavitySites

noncomputable def left0_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 0) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left0First.startPC w (mask :: rho))
      (stateAt s left0First.endPC (fourResult (left 0) s w) (mask :: rho)) := by
  have hwhole := run_leftCode 0 s left0First.startPC w rho hfit hstack hrun
  rw [← CavityFragmentChain.site_end left0First] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka left0First.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw left0First (left_advances 0)
      (stateAt s left0First.startPC w (mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp


noncomputable def left0_group (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 0) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left0First.startPC w (mask :: rho))
      (stateAt s left0First.endPC (fourResult (left 0) s w) (mask :: rho)) := by
  exact left0_core s w rho hfit hstack hrun hcode hfork hnp

noncomputable def left2_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 2) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left2First.startPC w (mask :: rho))
      (stateAt s left2First.endPC (fourResult (left 2) s w) (mask :: rho)) := by
  have hwhole := run_leftCode 2 s left2First.startPC w rho hfit hstack hrun
  rw [← CavityFragmentChain.site_end left2First] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka left2First.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw left2First (left_advances 2)
      (stateAt s left2First.startPC w (mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp


noncomputable def left2_group (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 2) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left2First.startPC w (mask :: rho))
      (stateAt s left2First.endPC (fourResult (left 2) s w) (mask :: rho)) := by
  exact left2_core s w rho hfit hstack hrun hcode hfork hnp

noncomputable def right_core (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hfit : ∀ k, (right k).Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s rightFirst.startPC w (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s rightFirst.endPC (fourResult right s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hwhole := run_rightCode s rightFirst.startPC w a b c d e rho hfit hstack hrun
  rw [← CavityFragmentChain.site_end rightFirst] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka rightFirst.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw rightFirst right_advances
      (stateAt s rightFirst.startPC w (a :: b :: c :: d :: e :: mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp


noncomputable def right_group (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hfit : ∀ k, (right k).Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s rightFirst.startPC w (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s rightFirst.endPC (fourResult right s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  exact right_core s w a b c d e rho hfit hstack hrun hcode hfork hnp

#print axioms left0_core
#print axioms left0_group
#print axioms left2_core
#print axioms left2_group
#print axioms right_core
#print axioms right_group

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavityExecution
