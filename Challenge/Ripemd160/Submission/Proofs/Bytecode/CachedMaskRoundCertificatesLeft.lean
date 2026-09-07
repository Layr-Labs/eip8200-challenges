import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundFacts
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundSitesLeft

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundCertificates

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace QuadRoundState QuadRoundTemplate QuadSites QuadSemantic

def gasSteps_leftNormal (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256) (n : CachedMaskRoundSitesLeft.NormalIndex)
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1006) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.leftPC (CachedMaskRoundSitesLeft.normalFin n).val) working (StackRoundTemplate.mask :: rho))
      (stateAt s (QuadSites.leftPC ((CachedMaskRoundSitesLeft.normalFin n).val + 1))
        (left4 word (CachedMaskRoundSitesLeft.normalFin n) working) (StackRoundTemplate.mask :: rho)) := by
  let k := CachedMaskRoundSitesLeft.normalFin n
  let site := CachedMaskRoundSitesLeft.normalRound n

  have hframe : (StackRoundTemplate.mask :: rho).length < 1007 := by
    simp only [List.length_cons]
    omega
  have hraw := ShiftedHoistHelper.run_left (k.val / 4) (by have h := k.isLt; omega) s site.helper.startPC
    (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k) (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k) site.returnPC (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k) (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k) working (QuadSites.leftConstant k) rho
    (fun h => leftConstant_zero k h) hstack hrun
    (leftRotation0_pos k) (leftRotation0_lt32 k) (leftRotation1_pos k) (leftRotation1_lt32 k)
    (leftRotation2_pos k) (leftRotation2_lt32 k) (leftRotation3_pos k) (leftRotation3_lt32 k)
  have ghelper := ShiftedHoistHelper.gasSteps_of_raw (ShiftedHoistHelper.leftTemplate (k.val / 4) (QuadSites.leftConstant k))
    (ShiftedHoistHelper.left_advances (k.val / 4) (by have h := k.isLt; omega) (QuadSites.leftConstant k))
    (k.val / 4) (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k) (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k) (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k) (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k) (QuadSites.leftConstant k)
    site.helper s site.returnPC working (StackRoundTemplate.mask :: rho) hraw hrun hcode hfork hnp
  have g := CachedMaskCalls.Normal.gasSteps_quad_of_helper (k.val / 4) (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k) (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k) (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k) (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k) (QuadSites.leftConstant k) (ShiftedHoistHelper.leftTemplate (k.val / 4) (QuadSites.leftConstant k))
    site s working (StackRoundTemplate.mask :: rho) hframe hrun hcode hfork hnp ghelper
  have hw := leftWorking_eq s word working k hwords

  have ha := leftActiveWords_eq s k hactive
  exact g.cast
    (by simp only [stateAt]; rw [CachedMaskRoundSitesLeft.normal_start n])
    (by
      simp only [stateAt, roundEntry, roundWords]
      rw [CachedMaskRoundSitesLeft.normal_end n, hw, ha]
      rfl)

#print axioms gasSteps_leftNormal

def gasSteps_leftFallthrough (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256) (group : Fin 3)
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1006) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.leftPC (CachedMaskRoundSitesLeft.fallthroughK group).val) working (StackRoundTemplate.mask :: rho))
      (stateAt s (QuadSites.leftPC ((CachedMaskRoundSitesLeft.fallthroughK group).val + 1))
        (left4 word (CachedMaskRoundSitesLeft.fallthroughK group) working) (StackRoundTemplate.mask :: rho)) := by
  let k := CachedMaskRoundSitesLeft.fallthroughK group
  let site := CachedMaskRoundSitesLeft.fallthroughRound group

  have hgroup : k.val / 4 = (CachedMaskRoundSitesLeft.groupFin group).val := by
    dsimp [k, CachedMaskRoundSitesLeft.fallthroughK]
    omega

  have hframe : (StackRoundTemplate.mask :: rho).length < 1007 := by
    simp only [List.length_cons]
    omega
  have hraw := ShiftedHoistHelper.run_left ((CachedMaskRoundSitesLeft.groupFin group).val) (by have h := (CachedMaskRoundSitesLeft.groupFin group).isLt; omega) s site.helper.startPC
    (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k) (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k) site.returnPC (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k) (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k) working (QuadSites.leftConstant k) rho
    (fun h => leftConstant_zero k (by omega)) hstack hrun
    (leftRotation0_pos k) (leftRotation0_lt32 k) (leftRotation1_pos k) (leftRotation1_lt32 k)
    (leftRotation2_pos k) (leftRotation2_lt32 k) (leftRotation3_pos k) (leftRotation3_lt32 k)
  have ghelper := ShiftedHoistHelper.gasSteps_of_raw (ShiftedHoistHelper.leftTemplate ((CachedMaskRoundSitesLeft.groupFin group).val) (QuadSites.leftConstant k))
    (ShiftedHoistHelper.left_advances ((CachedMaskRoundSitesLeft.groupFin group).val) (by have h := (CachedMaskRoundSitesLeft.groupFin group).isLt; omega) (QuadSites.leftConstant k))
    ((CachedMaskRoundSitesLeft.groupFin group).val) (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k) (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k) (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k) (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k) (QuadSites.leftConstant k)
    site.helper s site.returnPC working (StackRoundTemplate.mask :: rho) hraw hrun hcode hfork hnp
  have g := CachedMaskCalls.Fallthrough.gasSteps_of_helper ((CachedMaskRoundSitesLeft.groupFin group).val) (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k) (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k) (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k) (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k) (QuadSites.leftConstant k) (ShiftedHoistHelper.leftTemplate ((CachedMaskRoundSitesLeft.groupFin group).val) (QuadSites.leftConstant k))
    site s working (StackRoundTemplate.mask :: rho) hframe hrun hcode hfork hnp ghelper
  have hw := leftWorking_eq s word working k hwords

  rw [hgroup] at hw

  have ha := leftActiveWords_eq s k hactive
  exact g.cast
    (by simp only [stateAt]; rw [CachedMaskRoundSitesLeft.fallthrough_start group])
    (by
      simp only [stateAt, roundEntry, roundWords]
      rw [CachedMaskRoundSitesLeft.fallthrough_end group, hw, ha]
      rfl)

#print axioms gasSteps_leftFallthrough

noncomputable def gasSteps_leftQuad (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256) (k : Fin 20)
    (hk : 4 ≤ k.val ∧ (k.val < 8 ∨ 12 ≤ k.val))
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1006) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.leftPC k.val) working (StackRoundTemplate.mask :: rho))
      (stateAt s (QuadSites.leftPC (k.val + 1)) (left4 word k working) (StackRoundTemplate.mask :: rho)) := by
  apply Classical.choice
  fin_cases k <;> norm_num at hk

  · exact ⟨gasSteps_leftNormal s word working rho 0 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftNormal s word working rho 1 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftNormal s word working rho 2 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftFallthrough s word working rho 0 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftNormal s word working rho 3 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftNormal s word working rho 4 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftNormal s word working rho 5 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftFallthrough s word working rho 1 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftNormal s word working rho 6 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftNormal s word working rho 7 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftNormal s word working rho 8 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_leftFallthrough s word working rho 2 hwords hactive hstack hcode hfork hrun hnp⟩

#print axioms gasSteps_leftQuad

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundCertificates
