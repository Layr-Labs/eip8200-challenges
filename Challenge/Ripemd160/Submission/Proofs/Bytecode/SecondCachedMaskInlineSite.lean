import Challenge.Ripemd160.Submission.Proofs.Bytecode.SingleCachedMaskInline
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SingleCachedMaskInlineParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundFacts
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondCachedMaskInlineSite

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundTemplate
open SingleCachedMaskInlineParams

abbrev A := Artifact.submissionArtifact

def template : List Instr := CachedMaskQuadGroup.code (rightParams 0 1) 5

private theorem template_slice :
    (A.instructions.drop 2096).take template.length = template := by rfl

private theorem template_wellFormed : ∀ instruction ∈ template,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def site : GenericRoundSite A .Osaka template :=
  StackSiteBuilder.ofSlice _ 2096 template_slice (by
    change 2100 + template.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) QuadLayout.code_bound template_wellFormed (by decide)

theorem site_start : site.startPC = QuadSites.rightPC 1 := by rfl
theorem site_end : site.endPC = QuadSites.rightPC 2 := by rfl

def gasSteps_right1 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hwords : CachedMaskRoundCertificates.low32DenseWordsAt s word)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rho.length < 1001)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (CachedMaskRoundCertificates.stateAt s (QuadSites.rightPC 1) working
      (a :: b :: c :: d :: e :: mask :: rho))
      (CachedMaskRoundCertificates.stateAt s (QuadSites.rightPC 2)
        (CachedMaskRoundCertificates.right4 word 1 working) (a :: b :: c :: d :: e :: mask :: rho)) := by
  have core := SingleCachedMaskInline.gasSteps_right (rightParams 0 1) site
    s working a b c d e rho (right1_fits s hactive) hstack hcode hfork hrun hnp
  have hw : (rightParams 0 1).apply s working = CachedMaskRoundCertificates.right4 word 1 working :=
    CachedMaskRoundCertificates.rightWorking_eq s word working 1 hwords
  have whole := core
  exact whole.cast (by rw [site_start]; rfl) (by
    rw [site_end]
    change CachedMaskRoundCertificates.stateAt s (QuadSites.rightPC 2)
      ((rightParams 0 1).apply s working) (a :: b :: c :: d :: e :: mask :: rho) = _
    rw [hw])

#print axioms gasSteps_right1

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondCachedMaskInlineSite
