import Challenge.Ripemd160.Submission.Proofs.Bytecode.SingleCachedMaskInlineSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundFacts
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundSitesRight

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundCertificates

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace QuadRoundState QuadRoundTemplate QuadSites QuadSemantic

def gasSteps_rightNormal (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256) (n : CachedMaskRoundSitesRight.NormalIndex)
    (hwords : low32DenseWordsAt s word) (hactive : 25 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1001) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.rightPC (CachedMaskRoundSitesRight.normalFin n).val) working (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho))
      (stateAt s (QuadSites.rightPC ((CachedMaskRoundSitesRight.normalFin n).val + 1))
        (right4 word (CachedMaskRoundSitesRight.normalFin n) working) (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho)) := by
  let k := CachedMaskRoundSitesRight.normalFin n
  let site := CachedMaskRoundSitesRight.normalRound n

  have hframe : (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho).length < 1007 := by
    simp only [List.length_cons]
    omega
  have hraw := ShiftedHoistHelper.run_right (4 - k.val / 4) (by have h := k.isLt; omega) s site.helper.startPC
    (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k) (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k) site.returnPC (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k) (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k) working (QuadSites.rightConstant k) a b c d e rho
    (fun h => rightConstant_zero k h) hstack hrun
    (rightRotation0_pos k) (rightRotation0_lt32 k) (rightRotation1_pos k) (rightRotation1_lt32 k)
    (rightRotation2_pos k) (rightRotation2_lt32 k) (rightRotation3_pos k) (rightRotation3_lt32 k)
  have ghelper := ShiftedHoistHelper.gasSteps_of_raw (ShiftedHoistHelper.rightTemplate (4 - k.val / 4) (QuadSites.rightConstant k))
    (ShiftedHoistHelper.right_advances (4 - k.val / 4) (by have h := k.isLt; omega) (QuadSites.rightConstant k))
    (4 - k.val / 4) (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k) (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k) (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k) (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k) (QuadSites.rightConstant k)
    site.helper s site.returnPC working (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho) hraw hrun hcode hfork hnp
  have g := CachedMaskCalls.Normal.gasSteps_quad_of_helper (4 - k.val / 4) (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k) (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k) (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k) (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k) (QuadSites.rightConstant k) (ShiftedHoistHelper.rightTemplate (4 - k.val / 4) (QuadSites.rightConstant k))
    site s working (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho) hframe hrun hcode hfork hnp ghelper
  have hw := rightWorking_eq s word working k hwords

  have ha := rightActiveWords_eq s k hactive
  exact g.cast
    (by simp only [stateAt]; rw [CachedMaskRoundSitesRight.normal_start n])
    (by
      simp only [stateAt, roundEntry, roundWords]
      rw [CachedMaskRoundSitesRight.normal_end n, hw, ha]
      rfl)

#print axioms gasSteps_rightNormal

def gasSteps_rightFallthrough (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256) (group : Fin 4)
    (hwords : low32DenseWordsAt s word) (hactive : 25 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1001) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.rightPC (CachedMaskRoundSitesRight.fallthroughK group).val) working (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho))
      (stateAt s (QuadSites.rightPC ((CachedMaskRoundSitesRight.fallthroughK group).val + 1))
        (right4 word (CachedMaskRoundSitesRight.fallthroughK group) working) (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho)) := by
  let k := CachedMaskRoundSitesRight.fallthroughK group
  let site := CachedMaskRoundSitesRight.fallthroughRound group

  have hgroup : k.val / 4 = group.val := by
    dsimp [k, CachedMaskRoundSitesRight.fallthroughK]
    omega

  have hframe : (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho).length < 1007 := by
    simp only [List.length_cons]
    omega
  have hraw := ShiftedHoistHelper.run_right (4 - group.val) (by omega) s site.helper.startPC
    (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k) (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k) site.returnPC (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k) (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k) working (QuadSites.rightConstant k) a b c d e rho
    (fun h => rightConstant_zero k (by omega)) hstack hrun
    (rightRotation0_pos k) (rightRotation0_lt32 k) (rightRotation1_pos k) (rightRotation1_lt32 k)
    (rightRotation2_pos k) (rightRotation2_lt32 k) (rightRotation3_pos k) (rightRotation3_lt32 k)
  have ghelper := ShiftedHoistHelper.gasSteps_of_raw (ShiftedHoistHelper.rightTemplate (4 - group.val) (QuadSites.rightConstant k))
    (ShiftedHoistHelper.right_advances (4 - group.val) (by omega) (QuadSites.rightConstant k))
    (4 - group.val) (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k) (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k) (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k) (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k) (QuadSites.rightConstant k)
    site.helper s site.returnPC working (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho) hraw hrun hcode hfork hnp
  have g := CachedMaskCalls.Fallthrough.gasSteps_of_helper (4 - group.val) (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k) (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k) (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k) (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k) (QuadSites.rightConstant k) (ShiftedHoistHelper.rightTemplate (4 - group.val) (QuadSites.rightConstant k))
    site s working (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho) hframe hrun hcode hfork hnp ghelper
  have hw := rightWorking_eq s word working k hwords

  rw [hgroup] at hw

  have ha := rightActiveWords_eq s k hactive
  exact g.cast
    (by simp only [stateAt]; rw [CachedMaskRoundSitesRight.fallthrough_start group])
    (by
      simp only [stateAt, roundEntry, roundWords]
      rw [CachedMaskRoundSitesRight.fallthrough_end group, hw, ha]
      rfl)

#print axioms gasSteps_rightFallthrough

noncomputable def gasSteps_rightQuad (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256) (k : Fin 20)
    (hk : k.val < 16)
    (hwords : low32DenseWordsAt s word) (hactive : 25 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1001) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadSites.rightPC k.val) working (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho))
      (stateAt s (QuadSites.rightPC (k.val + 1)) (right4 word k working) (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho)) := by
  apply Classical.choice
  fin_cases k <;> norm_num at hk

  · exact ⟨SingleCachedMaskInlineSite.gasSteps_right0 s word working a b c d e rho hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 0 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 1 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightFallthrough s word working a b c d e rho 0 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 2 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 3 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 4 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightFallthrough s word working a b c d e rho 1 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 5 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 6 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 7 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightFallthrough s word working a b c d e rho 2 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 8 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 9 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightNormal s word working a b c d e rho 10 hwords hactive hstack hcode hfork hrun hnp⟩

  · exact ⟨gasSteps_rightFallthrough s word working a b c d e rho 3 hwords hactive hstack hcode hfork hrun hnp⟩

#print axioms gasSteps_rightQuad

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundCertificates
