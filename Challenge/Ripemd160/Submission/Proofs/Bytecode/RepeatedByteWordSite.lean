import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate

abbrev A := Artifact.submissionArtifact
def template : List Instr := RepeatedByteWord.code (UInt256.ofNat 97)

private theorem template_slice :
    (A.instructions.drop 22).take template.length = template := by rfl

private theorem template_wellFormed : ∀ instruction ∈ template,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def site : GenericRoundSite A .Osaka template :=
  StackSiteBuilder.ofSlice _ 22 template_slice (by
    change 22 + template.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) StackRoundData.artifact_code_bound template_wellFormed (by decide)

theorem site_start : site.startPC = UInt256.ofNat 33 := by rfl
theorem site_end : site.endPC = UInt256.ofNat 41 := by rfl

def gasSteps_fullWord (s : State) (rho : List UInt256) (hstack : rho.length < 1021)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 33, stack := rho}
      {s with pc := UInt256.ofNat 41, stack := KnownInputData.fullWord :: rho} := by
  have g := RepeatedByteWord.gasSteps_word (UInt256.ofNat 97) site
    s rho hstack hcode hfork hrun hnp
  exact g.cast (by rw [site_start]) (by rw [site_end, RepeatedByteWord.ascii_a])

#print axioms gasSteps_fullWord

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
