import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityRoundCertificatesLeft
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityRoundCertificatesRight
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityExecution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityResultSemantic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityLane

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackCompression QuadSemantic

abbrev Artifact := QuadSites.Artifact
abbrev low32DenseWordsAt := QuadSemantic.DenseWordsAt
abbrev stateAt := CavityRoundCertificates.stateAt

noncomputable def gasSteps_left80 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.leftPC 0) working rho)
      (stateAt s (QuadSites.leftPC 20) (leftRounds word 80 working) rho) := by
  let states := fun n => stateAt s (QuadSites.leftPC (n + 4))
    (leftRounds word (4 * (n + 4)) working) rho
  have step (i : Nat) (hi : i < 16) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨i + 4, by omega⟩
    have g := CavityRoundCertificates.gasSteps_leftQuad s word
      (leftRounds word (4 * (i + 4)) working) rho k (by dsimp [k]; omega)
      hwords hactive hstack hcode hfork hrun hnp
    have hnext : leftRounds word (4 * (i + 4 + 1)) working =
        CavityRoundCertificates.left4 word k (leftRounds word (4 * (i + 4)) working) := by
      rw [leftRounds_quad word (i + 4) working]
      rfl
    apply g.cast
    · rfl
    · change stateAt s (QuadSites.leftPC (i + 4 + 1))
          (CavityRoundCertificates.left4 word k (leftRounds word (4 * (i + 4)) working)) rho =
        stateAt s (QuadSites.leftPC (i + 1 + 4))
          (leftRounds word (4 * (i + 1 + 4)) working) rho
      rw [show i + 1 + 4 = i + 4 + 1 by omega, hnext]
  have rest := GasSteps.iterateBounded 16 step
  have first := CavityExecution.left_group s working rho
    (CavityResultSemantic.left_fits s hactive) hstack hrun hcode hfork hnp
  rw [CavityResultSemantic.left_result s word working hwords] at first
  exact first.trans rest

noncomputable def gasSteps_right80 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.rightPC 0) working rho)
      (stateAt s (QuadSites.rightPC 20) (rightRounds word 80 working) rho) := by
  let states := fun n => stateAt s (QuadSites.rightPC n)
    (rightRounds word (4 * n) working) rho
  have step (i : Nat) (hi : i < 16) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨i, by omega⟩
    have g := CavityRoundCertificates.gasSteps_rightQuad s word
      (rightRounds word (4 * i) working) rho k hi
      hwords hactive hstack hcode hfork hrun hnp
    have hnext : rightRounds word (4 * (i + 1)) working =
        CavityRoundCertificates.right4 word k (rightRounds word (4 * i) working) := by
      rw [rightRounds_quad word i working]
      rfl
    apply g.cast
    · rfl
    · change stateAt s (QuadSites.rightPC (i + 1))
          (CavityRoundCertificates.right4 word k (rightRounds word (4 * i) working)) rho =
        stateAt s (QuadSites.rightPC (i + 1))
          (rightRounds word (4 * (i + 1)) working) rho
      rw [hnext]
  have first := GasSteps.iterateBounded 16 step
  have last := CavityExecution.right_group s (rightRounds word 64 working) rho
    (CavityResultSemantic.right_fits s hactive) hstack hrun hcode hfork hnp
  rw [CavityResultSemantic.right_result_after64 s word working hwords] at last
  exact first.trans last

#print axioms gasSteps_left80
#print axioms gasSteps_right80

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityLane
