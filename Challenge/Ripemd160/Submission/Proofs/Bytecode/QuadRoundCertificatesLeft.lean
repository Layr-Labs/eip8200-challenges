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
private def gasSteps_leftNormal (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (n : QuadFallthroughSitesLeft.NormalIndex)
    (hwords : low32DenseWordsAt s word)
    (hactive : 61 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s (QuadSites.leftPC (QuadFallthroughSitesLeft.normalFin n).val)
        working rho)
      (stateAt s
        (QuadSites.leftPC ((QuadFallthroughSitesLeft.normalFin n).val + 1))
        (left4 word (QuadFallthroughSitesLeft.normalFin n) working) rho) := by
  let k := QuadFallthroughSitesLeft.normalFin n
  let site := QuadFallthroughSitesLeft.normalRound n
  have hraw :
      runInstrSeq
          (quadBeforeJumpTemplate (k.val / 4) (QuadSites.leftConstant k))
        (quadHelperEntry s site.helper.startPC
          (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
          (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k)
          site.returnPC (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
          (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k)
          working rho) =
      some (quadAfterHelperBeforeJump s
        (pcAfter site.helper.startPC
          (quadBeforeJumpTemplate (k.val / 4) (QuadSites.leftConstant k)))
        site.returnPC (k.val / 4) working
        (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
        (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k)
        (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
        (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k)
        (QuadSites.leftConstant k) rho) := by
    exact QuadRoundTrace.runInstrSeq_quad (k.val / 4) (by omega) s
      site.helper.startPC (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
      (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k) site.returnPC
      (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
      (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k) working
      (QuadSites.leftConstant k) rho
      (fun h => leftConstant_zero k h) hstack hrun
      (leftRotation0_le32 k) (leftRotation1_le32 k)
      (leftRotation2_le32 k) (leftRotation3_le32 k)
  have ghelper := QuadHelperTrace.gasSteps_helper_of_raw
    (j := k.val / 4) (hj := by omega)
    (p0 := QuadSites.leftAddress0 k) (p1 := QuadSites.leftAddress1 k)
    (p2 := QuadSites.leftAddress2 k) (p3 := QuadSites.leftAddress3 k)
    (r0 := QuadSites.leftRotation0 k) (r1 := QuadSites.leftRotation1 k)
    (r2 := QuadSites.leftRotation2 k) (r3 := QuadSites.leftRotation3 k)
    (constant := QuadSites.leftConstant k) site.helper s site.returnPC working rho
    hraw hrun hcode hfork hnp
  have g := QuadHelperTrace.gasSteps_quad_of_helper
    (j := k.val / 4) (p0 := QuadSites.leftAddress0 k)
    (p1 := QuadSites.leftAddress1 k) (p2 := QuadSites.leftAddress2 k)
    (p3 := QuadSites.leftAddress3 k)
    (r0 := QuadSites.leftRotation0 k) (r1 := QuadSites.leftRotation1 k)
    (r2 := QuadSites.leftRotation2 k) (r3 := QuadSites.leftRotation3 k)
    (constant := QuadSites.leftConstant k) site s working rho hstack hrun hcode
    hfork hnp ghelper
  have hw := leftWorking_eq s word working k hwords
  have ha := leftActiveWords_eq s k hactive
  exact g.cast
    (by
      simp only [stateAt]
      rw [QuadFallthroughSitesLeft.normal_start n])
    (by
      simp only [stateAt, StackRoundTrace.roundEntry, StackRoundTrace.roundWords]
      rw [QuadFallthroughSitesLeft.normal_end n, hw, ha]
      rfl)

private def gasSteps_leftFallthrough (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (group : Fin 5)
    (hwords : low32DenseWordsAt s word)
    (hactive : 61 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s (QuadSites.leftPC (QuadFallthroughSitesLeft.fallthroughK group).val)
        working rho)
      (stateAt s
        (QuadSites.leftPC ((QuadFallthroughSitesLeft.fallthroughK group).val + 1))
        (left4 word (QuadFallthroughSitesLeft.fallthroughK group) working) rho) := by
  let k := QuadFallthroughSitesLeft.fallthroughK group
  let site := QuadFallthroughSitesLeft.fallthroughRound group
  have hgroup : k.val / 4 = group.val := by
    dsimp [k, QuadFallthroughSitesLeft.fallthroughK]
    omega
  have hraw :
      runInstrSeq
          (quadBeforeJumpTemplate group.val (QuadSites.leftConstant k))
        (quadHelperEntry s site.helper.startPC
          (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
          (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k)
          site.returnPC (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
          (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k)
          working rho) =
      some (quadAfterHelperBeforeJump s
        (pcAfter site.helper.startPC
          (quadBeforeJumpTemplate group.val (QuadSites.leftConstant k)))
        site.returnPC group.val working
        (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
        (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k)
        (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
        (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k)
        (QuadSites.leftConstant k) rho) := by
    exact QuadRoundTrace.runInstrSeq_quad group.val (by omega) s
      site.helper.startPC (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
      (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k) site.returnPC
      (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
      (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k) working
      (QuadSites.leftConstant k) rho
      (fun h => leftConstant_zero k (hgroup.trans h)) hstack hrun
      (leftRotation0_le32 k) (leftRotation1_le32 k)
      (leftRotation2_le32 k) (leftRotation3_le32 k)
  have ghelper := QuadHelperTrace.gasSteps_helper_of_raw
    (j := group.val) (hj := by omega)
    (p0 := QuadSites.leftAddress0 k) (p1 := QuadSites.leftAddress1 k)
    (p2 := QuadSites.leftAddress2 k) (p3 := QuadSites.leftAddress3 k)
    (r0 := QuadSites.leftRotation0 k) (r1 := QuadSites.leftRotation1 k)
    (r2 := QuadSites.leftRotation2 k) (r3 := QuadSites.leftRotation3 k)
    (constant := QuadSites.leftConstant k) site.helper s site.returnPC working rho
    hraw hrun hcode hfork hnp
  have g := QuadFallthroughTrace.gasSteps_of_helper
    (j := group.val) (p0 := QuadSites.leftAddress0 k)
    (p1 := QuadSites.leftAddress1 k) (p2 := QuadSites.leftAddress2 k)
    (p3 := QuadSites.leftAddress3 k)
    (r0 := QuadSites.leftRotation0 k) (r1 := QuadSites.leftRotation1 k)
    (r2 := QuadSites.leftRotation2 k) (r3 := QuadSites.leftRotation3 k)
    (constant := QuadSites.leftConstant k) site s working rho hstack hrun hcode
    hfork hnp ghelper
  have hw := leftWorking_eq s word working k hwords
  rw [hgroup] at hw
  have ha := leftActiveWords_eq s k hactive
  exact g.cast
    (by
      simp only [stateAt]
      rw [QuadFallthroughSitesLeft.fallthrough_start group])
    (by
      simp only [stateAt, StackRoundTrace.roundEntry, StackRoundTrace.roundWords]
      rw [QuadFallthroughSitesLeft.fallthrough_end group, hw, ha]
      rfl)

def gasSteps_leftQuad (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256) (k : Fin 20)
    (hwords : low32DenseWordsAt s word)
    (hactive : 61 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s (QuadSites.leftPC k.val) working rho)
      (stateAt s (QuadSites.leftPC (k.val + 1)) (left4 word k working) rho) := by
  by_cases h : k.val % 4 = 3
  · rw [← fallthroughK_groupOf k h]
    exact gasSteps_leftFallthrough s word working rho (fallthroughGroupOf k)
      hwords hactive hstack hcode hfork hrun hnp
  · rw [← normalFin_indexOf k h]
    exact gasSteps_leftNormal s word working rho (normalIndexOf k h)
      hwords hactive hstack hcode hfork hrun hnp


end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates
