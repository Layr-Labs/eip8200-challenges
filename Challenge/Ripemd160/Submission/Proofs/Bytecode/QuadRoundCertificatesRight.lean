import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificateFacts

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-!
# H30b four-round certificates

This module composes the generic quad raw trace with the concrete combined
artifact sites.  It contains no outer frame, schedule, tail, or correctness
theorem.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression
private def gasSteps_rightNormal (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (n : QuadFallthroughSitesRight.NormalIndex)
    (hwords : low32DenseWordsAt s word)
    (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s (QuadSites.rightPC (QuadFallthroughSitesRight.normalFin n).val)
        working rho)
      (stateAt s
        (QuadSites.rightPC ((QuadFallthroughSitesRight.normalFin n).val + 1))
        (right4 word (QuadFallthroughSitesRight.normalFin n) working) rho) := by
  let k := QuadFallthroughSitesRight.normalFin n
  let site := QuadFallthroughSitesRight.normalRound n
  have hraw :
      runInstrSeq
          (quadBeforeJumpTemplate (4 - k.val / 4) (QuadSites.rightConstant k))
        (quadHelperEntry s site.helper.startPC
          (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
          (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k)
          site.returnPC (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
          (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k)
          working rho) =
      some (quadAfterHelperBeforeJump s
        (pcAfter site.helper.startPC
          (quadBeforeJumpTemplate (4 - k.val / 4) (QuadSites.rightConstant k)))
        site.returnPC (4 - k.val / 4) working
        (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
        (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k)
        (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
        (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k)
        (QuadSites.rightConstant k) rho) := by
    exact QuadRoundTrace.runInstrSeq_quad (4 - k.val / 4) (by omega) s
      site.helper.startPC (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
      (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k) site.returnPC
      (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
      (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k) working
      (QuadSites.rightConstant k) rho
      (fun h => rightConstant_zero k h) hstack hrun
      (rightRotation0_le32 k) (rightRotation1_le32 k)
      (rightRotation2_le32 k) (rightRotation3_le32 k)
  have ghelper := QuadHelperTrace.gasSteps_helper_of_raw
    (j := 4 - k.val / 4) (hj := by omega)
    (p0 := QuadSites.rightAddress0 k) (p1 := QuadSites.rightAddress1 k)
    (p2 := QuadSites.rightAddress2 k) (p3 := QuadSites.rightAddress3 k)
    (r0 := QuadSites.rightRotation0 k) (r1 := QuadSites.rightRotation1 k)
    (r2 := QuadSites.rightRotation2 k) (r3 := QuadSites.rightRotation3 k)
    (constant := QuadSites.rightConstant k) site.helper s site.returnPC working rho
    hraw hrun hcode hfork hnp
  have g := QuadHelperTrace.gasSteps_quad_of_helper
    (j := 4 - k.val / 4) (p0 := QuadSites.rightAddress0 k)
    (p1 := QuadSites.rightAddress1 k) (p2 := QuadSites.rightAddress2 k)
    (p3 := QuadSites.rightAddress3 k)
    (r0 := QuadSites.rightRotation0 k) (r1 := QuadSites.rightRotation1 k)
    (r2 := QuadSites.rightRotation2 k) (r3 := QuadSites.rightRotation3 k)
    (constant := QuadSites.rightConstant k) site s working rho hstack hrun hcode
    hfork hnp ghelper
  have hw := rightWorking_eq s word working k hwords
  have ha := rightActiveWords_eq s k hactive
  exact g.cast
    (by
      simp only [stateAt]
      rw [QuadFallthroughSitesRight.normal_start n])
    (by
      simp only [stateAt, StackRoundTrace.roundEntry, StackRoundTrace.roundWords]
      rw [QuadFallthroughSitesRight.normal_end n, hw, ha]
      rfl)

private def gasSteps_rightFallthrough (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (group : Fin 5)
    (hwords : low32DenseWordsAt s word)
    (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s (QuadSites.rightPC (QuadFallthroughSitesRight.fallthroughK group).val)
        working rho)
      (stateAt s
        (QuadSites.rightPC ((QuadFallthroughSitesRight.fallthroughK group).val + 1))
        (right4 word (QuadFallthroughSitesRight.fallthroughK group) working) rho) := by
  let k := QuadFallthroughSitesRight.fallthroughK group
  let site := QuadFallthroughSitesRight.fallthroughRound group
  have hgroup : k.val / 4 = group.val := by
    dsimp [k, QuadFallthroughSitesRight.fallthroughK]
    omega
  have hraw :
      runInstrSeq
          (quadBeforeJumpTemplate (4 - group.val) (QuadSites.rightConstant k))
        (quadHelperEntry s site.helper.startPC
          (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
          (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k)
          site.returnPC (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
          (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k)
          working rho) =
      some (quadAfterHelperBeforeJump s
        (pcAfter site.helper.startPC
          (quadBeforeJumpTemplate (4 - group.val) (QuadSites.rightConstant k)))
        site.returnPC (4 - group.val) working
        (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
        (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k)
        (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
        (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k)
        (QuadSites.rightConstant k) rho) := by
    exact QuadRoundTrace.runInstrSeq_quad (4 - group.val) (by omega) s
      site.helper.startPC (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
      (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k) site.returnPC
      (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
      (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k) working
      (QuadSites.rightConstant k) rho
      (fun h => rightConstant_zero k (by omega)) hstack hrun
      (rightRotation0_le32 k) (rightRotation1_le32 k)
      (rightRotation2_le32 k) (rightRotation3_le32 k)
  have ghelper := QuadHelperTrace.gasSteps_helper_of_raw
    (j := 4 - group.val) (hj := by omega)
    (p0 := QuadSites.rightAddress0 k) (p1 := QuadSites.rightAddress1 k)
    (p2 := QuadSites.rightAddress2 k) (p3 := QuadSites.rightAddress3 k)
    (r0 := QuadSites.rightRotation0 k) (r1 := QuadSites.rightRotation1 k)
    (r2 := QuadSites.rightRotation2 k) (r3 := QuadSites.rightRotation3 k)
    (constant := QuadSites.rightConstant k) site.helper s site.returnPC working rho
    hraw hrun hcode hfork hnp
  have g := QuadFallthroughTrace.gasSteps_of_helper
    (j := 4 - group.val) (p0 := QuadSites.rightAddress0 k)
    (p1 := QuadSites.rightAddress1 k) (p2 := QuadSites.rightAddress2 k)
    (p3 := QuadSites.rightAddress3 k)
    (r0 := QuadSites.rightRotation0 k) (r1 := QuadSites.rightRotation1 k)
    (r2 := QuadSites.rightRotation2 k) (r3 := QuadSites.rightRotation3 k)
    (constant := QuadSites.rightConstant k) site s working rho hstack hrun hcode
    hfork hnp ghelper
  have hw := rightWorking_eq s word working k hwords
  rw [hgroup] at hw
  have ha := rightActiveWords_eq s k hactive
  exact g.cast
    (by
      simp only [stateAt]
      rw [QuadFallthroughSitesRight.fallthrough_start group])
    (by
      simp only [stateAt, StackRoundTrace.roundEntry, StackRoundTrace.roundWords]
      rw [QuadFallthroughSitesRight.fallthrough_end group, hw, ha]
      rfl)

def gasSteps_rightQuad (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256) (k : Fin 20)
    (hwords : low32DenseWordsAt s word)
    (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s (QuadSites.rightPC k.val) working rho)
      (stateAt s (QuadSites.rightPC (k.val + 1)) (right4 word k working) rho) := by
  by_cases h : k.val % 4 = 3
  · rw [← rightFallthroughK_groupOf k h]
    exact gasSteps_rightFallthrough s word working rho (fallthroughGroupOf k)
      hwords hactive hstack hcode hfork hrun hnp
  · rw [← rightNormalFin_indexOf k h]
    exact gasSteps_rightNormal s word working rho (normalIndexOf k h)
      hwords hactive hstack hcode hfork hrun hnp


end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates
