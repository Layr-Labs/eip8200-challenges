import Challenge.Ripemd160.Submission.Proofs.Bytecode.SingleCachedMaskInline
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SingleCachedMaskInlineParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundFacts
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ThirdCachedMaskInlineSite

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundTemplate
open SingleCachedMaskInlineParams

abbrev A := Artifact.submissionArtifact

def template : List Instr := CachedMaskQuadGroup.code (rightParams 0 2) 5

private theorem template_slice :
    (A.instructions.drop 2398).take template.length = template := by rfl

private theorem template_wellFormed : ∀ instruction ∈ template,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def site : GenericRoundSite A .Osaka template :=
  StackSiteBuilder.ofSlice _ 2398 template_slice (by
    change 2398 + template.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) QuadLayout.code_bound template_wellFormed (by decide)

def destination : LocatedSite A .Osaka where
  located :=
    { index := 2510
      instruction := .op .JUMPDEST
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := QuadSites.rightReturnPC 2
  pc_eq := QuadLayout.pc_toNat_instructionPC _

theorem site_start : site.startPC = QuadSites.rightPC 2 := by rfl
theorem site_end : site.endPC = destination.pc := by rfl
theorem destination_next : destination.pc.succ = QuadSites.rightPC 3 := by rfl

def gasSteps_right2 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hwords : CachedMaskRoundCertificates.low32DenseWordsAt s word)
    (hactive : 25 ≤ s.activeWords.toNat) (hstack : rho.length < 1001)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (CachedMaskRoundCertificates.stateAt s (QuadSites.rightPC 2) working
      (a :: b :: c :: d :: e :: mask :: rho))
      (CachedMaskRoundCertificates.stateAt s (QuadSites.rightPC 3)
        (CachedMaskRoundCertificates.right4 word 2 working) (a :: b :: c :: d :: e :: mask :: rho)) := by
  have core := SingleCachedMaskInline.gasSteps_right (rightParams 0 2) site
    s working a b c d e rho (right2_fits s hactive) hstack hcode hfork hrun hnp
  have hw : (rightParams 0 2).apply s working = CachedMaskRoundCertificates.right4 word 2 working :=
    CachedMaskRoundCertificates.rightWorking_eq s word working 2 hwords
  let w := (rightParams 0 2).apply s working
  have hcap : ([w.a, w.b, w.c, w.d, w.e] ++
      factor :: a :: b :: c :: d :: e :: mask :: rho).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have finish := SingleCachedMaskInline.gasSteps_destination destination rfl s
    ([w.a, w.b, w.c, w.d, w.e] ++ factor :: a :: b :: c :: d :: e :: mask :: rho)
    hcap hcode hfork hrun hnp
  rw [← site_end] at finish
  have whole := core.trans finish
  exact whole.cast (by rw [site_start]; rfl) (by
    rw [site_end, destination_next]
    change CachedMaskRoundCertificates.stateAt s (QuadSites.rightPC 3)
      ((rightParams 0 2).apply s working) (a :: b :: c :: d :: e :: mask :: rho) = _
    rw [hw])

#print axioms gasSteps_right2

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ThirdCachedMaskInlineSite
