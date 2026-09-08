import Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheSites

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheExecution

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace CavityQuadGroup CachedMaskQuadGroup
open WordCacheGroups

abbrev A := Artifact.submissionArtifact

noncomputable def gasSteps_left0 (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1003) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadLayout.leftPC 0) w (mask :: (words s ++ rho)))
      (stateAt s (QuadLayout.leftPC 4)
        (CachedMaskQuadGroup.fourResult (CachedMaskParams.left 0) s w) (mask :: (words s ++ rho))) := by
  have hwhole := WordCacheGroups.run_left0 s WordCacheSites.left0.startPC w rho
    hactive hstack hrun
  rw [← CavityFragmentChain.site_end WordCacheSites.left0] at hwhole
  have g : GasSteps (stateAt s WordCacheSites.left0.startPC w
      (mask :: (words s ++ rho)))
      (stateAt s WordCacheSites.left0.endPC
        (CachedMaskQuadGroup.fourResult (CachedMaskParams.left 0) s w) (mask :: (words s ++ rho))) := by
    apply Stepper.runLocatedBlock_sound A .Osaka WordCacheSites.left0.path
    · simpa [stateAt, roundEntry] using hcode
    · simpa [stateAt, roundEntry] using hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw WordCacheSites.left0
        WordCacheSites.left0_advances
        (stateAt s WordCacheSites.left0.startPC w (mask :: (words s ++ rho))) rfl]
      exact hwhole
    · simpa [stateAt, roundEntry] using hrun
    · simpa [stateAt, roundEntry] using hnp
  exact g.cast (by rfl) (by rfl)

noncomputable def gasSteps_left2 (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1003) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadLayout.leftPC 8) w (mask :: (words s ++ rho)))
      (stateAt s (QuadLayout.leftPC 12)
        (CallsConstantGroup.cachedFourResult CallsConstantParams.left2 s w) (mask :: (words s ++ rho))) := by
  have hwhole := WordCacheGroups.run_left2 s WordCacheSites.left2.startPC w rho
    hactive hstack hrun
  rw [← CavityFragmentChain.site_end WordCacheSites.left2] at hwhole
  have g : GasSteps (stateAt s WordCacheSites.left2.startPC w
      (mask :: (words s ++ rho)))
      (stateAt s WordCacheSites.left2.endPC
        (CallsConstantGroup.cachedFourResult CallsConstantParams.left2 s w) (mask :: (words s ++ rho))) := by
    apply Stepper.runLocatedBlock_sound A .Osaka WordCacheSites.left2.path
    · simpa [stateAt, roundEntry] using hcode
    · simpa [stateAt, roundEntry] using hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw WordCacheSites.left2
        WordCacheSites.left2_advances
        (stateAt s WordCacheSites.left2.startPC w (mask :: (words s ++ rho))) rfl]
      exact hwhole
    · simpa [stateAt, roundEntry] using hrun
    · simpa [stateAt, roundEntry] using hnp
  exact g.cast (by rfl) (by rfl)

noncomputable def gasSteps_left4 (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1003) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadLayout.leftPC 16) w (mask :: (words s ++ rho)))
      (stateAt s (QuadLayout.leftPC 20)
        (CallsConstantGroup.cachedFourResult CallsConstantParams.left4 s w) (mask :: (words s ++ rho))) := by
  have hwhole := WordCacheGroups.run_left4 s WordCacheSites.left4.startPC w rho
    hactive hstack hrun
  rw [← CavityFragmentChain.site_end WordCacheSites.left4] at hwhole
  have g : GasSteps (stateAt s WordCacheSites.left4.startPC w
      (mask :: (words s ++ rho)))
      (stateAt s WordCacheSites.left4.endPC
        (CallsConstantGroup.cachedFourResult CallsConstantParams.left4 s w) (mask :: (words s ++ rho))) := by
    apply Stepper.runLocatedBlock_sound A .Osaka WordCacheSites.left4.path
    · simpa [stateAt, roundEntry] using hcode
    · simpa [stateAt, roundEntry] using hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw WordCacheSites.left4
        WordCacheSites.left4_advances
        (stateAt s WordCacheSites.left4.startPC w (mask :: (words s ++ rho))) rfl]
      exact hwhole
    · simpa [stateAt, roundEntry] using hrun
    · simpa [stateAt, roundEntry] using hnp
  exact g.cast (by rfl) (by rfl)

noncomputable def gasSteps_right0 (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadLayout.rightPC 0) w (a :: b :: c :: d :: e :: mask :: (words s ++ rho)))
      (stateAt s (QuadLayout.rightPC 4)
        (CallsConstantGroup.cachedFourResult CallsConstantParams.right0 s w) (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
  have hwhole := WordCacheGroups.run_right0 s WordCacheSites.right0.startPC w a b c d e rho
    hactive hstack hrun
  rw [← CavityFragmentChain.site_end WordCacheSites.right0] at hwhole
  have g : GasSteps (stateAt s WordCacheSites.right0.startPC w
      (a :: b :: c :: d :: e :: mask :: (words s ++ rho)))
      (stateAt s WordCacheSites.right0.endPC
        (CallsConstantGroup.cachedFourResult CallsConstantParams.right0 s w) (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
    apply Stepper.runLocatedBlock_sound A .Osaka WordCacheSites.right0.path
    · simpa [stateAt, roundEntry] using hcode
    · simpa [stateAt, roundEntry] using hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw WordCacheSites.right0
        WordCacheSites.right0_advances
        (stateAt s WordCacheSites.right0.startPC w (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) rfl]
      exact hwhole
    · simpa [stateAt, roundEntry] using hrun
    · simpa [stateAt, roundEntry] using hnp
  exact g.cast (by rfl) (by rfl)

noncomputable def gasSteps_right1 (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadLayout.rightPC 4) w (a :: b :: c :: d :: e :: mask :: (words s ++ rho)))
      (stateAt s (QuadLayout.rightPC 8)
        (CallsConstantGroup.cachedFourResult CallsConstantParams.right1 s w) (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
  have hwhole := WordCacheGroups.run_right1 s WordCacheSites.right1.startPC w a b c d e rho
    hactive hstack hrun
  rw [← CavityFragmentChain.site_end WordCacheSites.right1] at hwhole
  have g : GasSteps (stateAt s WordCacheSites.right1.startPC w
      (a :: b :: c :: d :: e :: mask :: (words s ++ rho)))
      (stateAt s WordCacheSites.right1.endPC
        (CallsConstantGroup.cachedFourResult CallsConstantParams.right1 s w) (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
    apply Stepper.runLocatedBlock_sound A .Osaka WordCacheSites.right1.path
    · simpa [stateAt, roundEntry] using hcode
    · simpa [stateAt, roundEntry] using hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw WordCacheSites.right1
        WordCacheSites.right1_advances
        (stateAt s WordCacheSites.right1.startPC w (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) rfl]
      exact hwhole
    · simpa [stateAt, roundEntry] using hrun
    · simpa [stateAt, roundEntry] using hnp
  exact g.cast (by rfl) (by rfl)

noncomputable def gasSteps_right2 (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadLayout.rightPC 8) w (a :: b :: c :: d :: e :: mask :: (words s ++ rho)))
      (stateAt s (QuadLayout.rightPC 12)
        (CallsConstantGroup.cachedFourResult CallsConstantParams.right2 s w) (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
  have hwhole := WordCacheGroups.run_right2 s WordCacheSites.right2.startPC w a b c d e rho
    hactive hstack hrun
  rw [← CavityFragmentChain.site_end WordCacheSites.right2] at hwhole
  have g : GasSteps (stateAt s WordCacheSites.right2.startPC w
      (a :: b :: c :: d :: e :: mask :: (words s ++ rho)))
      (stateAt s WordCacheSites.right2.endPC
        (CallsConstantGroup.cachedFourResult CallsConstantParams.right2 s w) (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
    apply Stepper.runLocatedBlock_sound A .Osaka WordCacheSites.right2.path
    · simpa [stateAt, roundEntry] using hcode
    · simpa [stateAt, roundEntry] using hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw WordCacheSites.right2
        WordCacheSites.right2_advances
        (stateAt s WordCacheSites.right2.startPC w (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) rfl]
      exact hwhole
    · simpa [stateAt, roundEntry] using hrun
    · simpa [stateAt, roundEntry] using hnp
  exact g.cast (by rfl) (by rfl)

noncomputable def gasSteps_right4 (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadLayout.rightPC 16) w (a :: b :: c :: d :: e :: mask :: (words s ++ rho)))
      (stateAt s (QuadLayout.rightPC 20)
        (CachedMaskQuadGroup.fourResult CachedMaskParams.right s w) (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
  have hwhole := WordCacheGroups.run_right4 s WordCacheSites.right4.startPC w a b c d e rho
    hactive hstack hrun
  rw [← CavityFragmentChain.site_end WordCacheSites.right4] at hwhole
  have g : GasSteps (stateAt s WordCacheSites.right4.startPC w
      (a :: b :: c :: d :: e :: mask :: (words s ++ rho)))
      (stateAt s WordCacheSites.right4.endPC
        (CachedMaskQuadGroup.fourResult CachedMaskParams.right s w) (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
    apply Stepper.runLocatedBlock_sound A .Osaka WordCacheSites.right4.path
    · simpa [stateAt, roundEntry] using hcode
    · simpa [stateAt, roundEntry] using hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw WordCacheSites.right4
        WordCacheSites.right4_advances
        (stateAt s WordCacheSites.right4.startPC w (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) rfl]
      exact hwhole
    · simpa [stateAt, roundEntry] using hrun
    · simpa [stateAt, roundEntry] using hnp
  exact g.cast (by rfl) (by rfl)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheExecution
