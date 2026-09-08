import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundCertificatesLeft
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundCertificatesRight
import Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheExecution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantGroup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantParams

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskLane

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackCompression QuadSemantic CachedMaskRoundCertificates

abbrev Artifact := QuadSites.Artifact
abbrev low32DenseWordsAt := QuadSemantic.DenseWordsAt
abbrev stateAt := CachedMaskRoundCertificates.stateAt

private noncomputable def left_span (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256) (start count : Nat)
    (hbound : start + count ≤ 20)
    (hallowed : ∀ i, i < count →
      4 ≤ start + i ∧ (start + i < 8 ∨ 12 ≤ start + i) ∧ start + i < 16)
    (hwords : low32DenseWordsAt s word) (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1006) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.leftPC start) (leftRounds word (4 * start) working)
      (StackRoundTemplate.mask :: rho))
      (stateAt s (QuadSites.leftPC (start + count))
        (leftRounds word (4 * (start + count)) working) (StackRoundTemplate.mask :: rho)) := by
  let states := fun n => stateAt s (QuadSites.leftPC (start + n))
    (leftRounds word (4 * (start + n)) working) (StackRoundTemplate.mask :: rho)
  have step (i : Nat) (hi : i < count) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨start + i, by omega⟩
    have g := CachedMaskRoundCertificates.gasSteps_leftQuad s word
      (leftRounds word (4 * (start + i)) working) rho k (hallowed i hi)
      hwords hactive hstack hcode hfork hrun hnp
    have hnext : leftRounds word (4 * (start + i + 1)) working =
        left4 word k (leftRounds word (4 * (start + i)) working) := by
      rw [leftRounds_quad word (start + i) working]
      rfl
    apply g.cast
    · rfl
    · change stateAt s (QuadSites.leftPC (start + i + 1))
          (left4 word k (leftRounds word (4 * (start + i)) working))
          (StackRoundTemplate.mask :: rho) =
        stateAt s (QuadSites.leftPC (start + (i + 1)))
          (leftRounds word (4 * (start + (i + 1))) working) (StackRoundTemplate.mask :: rho)
      rw [show start + (i + 1) = start + i + 1 by omega, hnext]
  have g := GasSteps.iterateBounded count step
  simpa only [states, Nat.add_zero] using g

noncomputable def gasSteps_left80 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hwords : low32DenseWordsAt s word) (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1003) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.leftPC 0) working (StackRoundTemplate.mask :: (WordCacheGroups.words s ++ rho)))
      (stateAt s (QuadSites.leftPC 20) (leftRounds word 80 working)
        (StackRoundTemplate.mask :: (WordCacheGroups.words s ++ rho))) := by
  have cacheBound : (WordCacheGroups.words s ++ rho).length < 1006 := by
    simp only [WordCacheGroups.words, WordCacheTemplates.words, List.length_append, List.length_cons, List.length_nil]
    omega
  have first := WordCacheExecution.gasSteps_left0 s working rho
    hactive hstack hrun hcode hfork hnp
  have firstResult : CachedMaskQuadGroup.fourResult (CachedMaskParams.left 0) s working =
      leftRounds word 16 working :=
    CachedMaskParams.left_result_after s word working 0 hwords
  rw [firstResult] at first
  have second := left_span s word working (WordCacheGroups.words s ++ rho) 4 4 (by decide)
    (by intro i hi; omega) hwords hactive cacheBound hcode hfork hrun hnp
  have third := WordCacheExecution.gasSteps_left2 s (leftRounds word 32 working) rho
    hactive hstack hrun hcode hfork hnp
  have thirdResult : CallsConstantGroup.cachedFourResult CallsConstantParams.left2 s
      (leftRounds word 32 working) = leftRounds word 48 working :=
    CallsConstantParams.left2_result_after s word working hwords
  rw [thirdResult] at third
  have last := left_span s word working (WordCacheGroups.words s ++ rho) 12 4 (by decide)
    (by intro i hi; omega) hwords hactive cacheBound hcode hfork hrun hnp
  have fourth := WordCacheExecution.gasSteps_left4 s (leftRounds word 64 working) rho
    hactive hstack hrun hcode hfork hnp
  have fourthResult : CallsConstantGroup.cachedFourResult CallsConstantParams.left4 s
      (leftRounds word 64 working) = leftRounds word 80 working :=
    CallsConstantParams.left4_result_after s word working hwords
  rw [fourthResult] at fourth
  exact (((first.trans second).trans third).trans last).trans fourth

noncomputable def gasSteps_right80 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hwords : low32DenseWordsAt s word) (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 998) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.rightPC 0) working
      (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: (WordCacheGroups.words s ++ rho)))
      (stateAt s (QuadSites.rightPC 20) (rightRounds word 80 working)
        (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: (WordCacheGroups.words s ++ rho))) := by
  have cacheBound : (WordCacheGroups.words s ++ rho).length < 1001 := by
    simp only [WordCacheGroups.words, WordCacheTemplates.words, List.length_append, List.length_cons, List.length_nil]
    omega
  have first := WordCacheExecution.gasSteps_right0 s working a b c d e rho
    hactive hstack hrun hcode hfork hnp
  have firstResult : CallsConstantGroup.cachedFourResult CallsConstantParams.right0 s working =
      rightRounds word 16 working := by
    simpa only [StackCompression.rightRounds] using
      CallsConstantParams.right0_result_after s word working hwords
  rw [firstResult] at first
  have second := WordCacheExecution.gasSteps_right1 s (rightRounds word 16 working)
      a b c d e rho hactive
      hstack hrun hcode hfork hnp
  rw [CallsConstantParams.right1_result_after s word working hwords] at second
  have third := WordCacheExecution.gasSteps_right2 s (rightRounds word 32 working)
      a b c d e rho hactive
      hstack hrun hcode hfork hnp
  rw [CallsConstantParams.right2_result_after s word working hwords] at third

  let states := fun n => stateAt s (QuadSites.rightPC (12 + n))
    (rightRounds word (48 + 4 * n) working)
    (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: (WordCacheGroups.words s ++ rho))
  have step (i : Nat) (hi : i < 4) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨12 + i, by omega⟩
    have g := CachedMaskRoundCertificates.gasSteps_rightQuad s word
      (rightRounds word (48 + 4 * i) working) a b c d e (WordCacheGroups.words s ++ rho) k (by dsimp [k]; omega)
      hwords hactive cacheBound hcode hfork hrun hnp
    have hnext : rightRounds word (48 + 4 * (i + 1)) working =
        right4 word k (rightRounds word (48 + 4 * i) working) := by
      rw [show 48 + 4 * (i + 1) = 4 * ((12 + i) + 1) by omega,
        rightRounds_quad word (12 + i) working,
        show 4 * (12 + i) = 48 + 4 * i by omega]
      simp [right4, QuadSemantic.quadIndex, k, Nat.mul_add, Nat.add_comm]
    apply g.cast
    · rfl
    · change stateAt s (QuadSites.rightPC (12 + i + 1))
          (right4 word k (rightRounds word (48 + 4 * i) working))
          (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: (WordCacheGroups.words s ++ rho)) =
        stateAt s (QuadSites.rightPC (12 + (i + 1)))
          (rightRounds word (48 + 4 * (i + 1)) working)
          (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: (WordCacheGroups.words s ++ rho))
      rw [show 12 + (i + 1) = 12 + i + 1 by omega, hnext]
  have normal := GasSteps.iterateBounded 4 step
  have last := WordCacheExecution.gasSteps_right4 s (rightRounds word 64 working)
    a b c d e rho hactive
    hstack hrun hcode hfork hnp
  rw [CachedMaskParams.right_result_after64 s word working hwords] at last
  exact (((first.trans second).trans third).trans normal).trans last

#print axioms gasSteps_left80
#print axioms gasSteps_right80

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskLane
