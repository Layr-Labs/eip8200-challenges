import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCaps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantGroup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantSites
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

noncomputable abbrev left0_group := left0_core

noncomputable def left2_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, (CallsConstantParams.left2 k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s CallsConstantSites.left2.startPC w (mask :: rho))
      (stateAt s CallsConstantSites.left2.endPC
        (CallsConstantGroup.cachedFourResult CallsConstantParams.left2 s w)
        (mask :: rho)) := by
  have hwhole := CallsConstantGroup.run_left_cached_four
    CallsConstantParams.left2 0 (CallsConstantParams.left2 0).constant s
    CallsConstantSites.left2.startPC w rho
    (fun k => CallsConstantParams.left2_function k)
    (fun k => CallsConstantParams.left2_constant k) hfit hstack hrun
  have hsite_end : CallsConstantSites.left2.endPC =
      pcAfter CallsConstantSites.left2.startPC
        (CallsConstantGroup.cachedFourCode CallsConstantParams.left2 0
          (CallsConstantParams.left2 0).constant 0) := by
    simpa only [CallsConstantParams.left2Code] using
      (CavityFragmentChain.site_end CallsConstantSites.left2)
  rw [← hsite_end] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka CallsConstantSites.left2.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw CallsConstantSites.left2
      CallsConstantSites.left2_advances
      (stateAt s CallsConstantSites.left2.startPC w (mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp

noncomputable abbrev left2_group := left2_core

noncomputable def right0_core (s : State) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hfit : ∀ k, (CallsConstantParams.right0 k).Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s CallsConstantSites.right0.startPC w
      (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s CallsConstantSites.right0.endPC
        (CallsConstantGroup.cachedFourResult CallsConstantParams.right0 s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hwhole := CallsConstantGroup.run_right_cached_four
    CallsConstantParams.right0 2 (CallsConstantParams.right0 0).constant s
    CallsConstantSites.right0.startPC w a b c d e rho
    (fun k => CallsConstantParams.right0_function k)
    (fun k => CallsConstantParams.right0_constant k) hfit hstack hrun
  have hsite_end : CallsConstantSites.right0.endPC =
      pcAfter CallsConstantSites.right0.startPC
        (CallsConstantGroup.cachedFourCode CallsConstantParams.right0 2
          (CallsConstantParams.right0 0).constant 5) := by
    simpa only [CallsConstantParams.right0Code] using
      (CavityFragmentChain.site_end CallsConstantSites.right0)
  rw [← hsite_end] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka CallsConstantSites.right0.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw CallsConstantSites.right0
      CallsConstantSites.right0_advances
      (stateAt s CallsConstantSites.right0.startPC w
        (a :: b :: c :: d :: e :: mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp

noncomputable abbrev right0_group := right0_core

noncomputable def right1_core (s : State) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hfit : ∀ k, (CallsConstantParams.right1 k).Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s CallsConstantSites.right1.startPC w
      (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s CallsConstantSites.right1.endPC
        (CallsConstantGroup.cachedFourResult CallsConstantParams.right1 s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hwhole := CallsConstantGroup.run_right_cached_four
    CallsConstantParams.right1 1 (CallsConstantParams.right1 0).constant s
    CallsConstantSites.right1.startPC w a b c d e rho
    (fun k => CallsConstantParams.right1_function k)
    (fun k => CallsConstantParams.right1_constant k) hfit hstack hrun
  have hsite_end : CallsConstantSites.right1.endPC =
      pcAfter CallsConstantSites.right1.startPC
        (CallsConstantGroup.cachedFourCode CallsConstantParams.right1 1
          (CallsConstantParams.right1 0).constant 5) := by
    simpa only [CallsConstantParams.right1Code] using
      (CavityFragmentChain.site_end CallsConstantSites.right1)
  rw [← hsite_end] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka CallsConstantSites.right1.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw CallsConstantSites.right1
      CallsConstantSites.right1_advances
      (stateAt s CallsConstantSites.right1.startPC w
        (a :: b :: c :: d :: e :: mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp

noncomputable abbrev right1_group := right1_core

noncomputable def right2_core (s : State) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hfit : ∀ k, (CallsConstantParams.right2 k).Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s CallsConstantSites.right2.startPC w
      (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s CallsConstantSites.right2.endPC
        (CallsConstantGroup.cachedFourResult CallsConstantParams.right2 s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hwhole := CallsConstantGroup.run_right_cached_four
    CallsConstantParams.right2 0 (CallsConstantParams.right2 0).constant s
    CallsConstantSites.right2.startPC w a b c d e rho
    (fun k => CallsConstantParams.right2_function k)
    (fun k => CallsConstantParams.right2_constant k) hfit hstack hrun
  have hsite_end : CallsConstantSites.right2.endPC =
      pcAfter CallsConstantSites.right2.startPC
        (CallsConstantGroup.cachedFourCode CallsConstantParams.right2 0
          (CallsConstantParams.right2 0).constant 5) := by
    simpa only [CallsConstantParams.right2Code] using
      (CavityFragmentChain.site_end CallsConstantSites.right2)
  rw [← hsite_end] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka CallsConstantSites.right2.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw CallsConstantSites.right2
      CallsConstantSites.right2_advances
      (stateAt s CallsConstantSites.right2.startPC w
        (a :: b :: c :: d :: e :: mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp

noncomputable abbrev right2_group := right2_core

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

noncomputable abbrev right_group := right_core

#print axioms left0_core
#print axioms left0_group
#print axioms left2_core
#print axioms left2_group
#print axioms right0_core
#print axioms right0_group
#print axioms right1_core
#print axioms right1_group
#print axioms right2_core
#print axioms right2_group
#print axioms right_core
#print axioms right_group

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavityExecution
