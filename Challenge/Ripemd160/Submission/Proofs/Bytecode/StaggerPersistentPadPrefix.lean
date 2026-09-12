import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPadPrefix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate
def prefixTemplate : List Instr := [.op .JUMPDEST, .op .JUMPDEST]
theorem prefix_slice :
    (Artifact.submissionArtifact.instructions.drop 285).take prefixTemplate.length = prefixTemplate := by rfl
def prefixSite : GenericRoundSite Artifact.submissionArtifact .Osaka prefixTemplate :=
  StackSiteBuilder.ofSlice prefixTemplate 285 prefix_slice
    (by change 285 + prefixTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := prefixTemplate) (by decide))
    (by decide)
theorem prefix_pc : prefixSite.startPC = UInt256.ofNat 448 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 285) = UInt256.ofNat 448
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem prefix_advances : ∀ instruction ∈ prefixTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

def gasSteps_prefix (s : State) (stack : List UInt256)
    (hstack : stack.length ≤ 1019) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 448, stack := stack}
      {s with pc := UInt256.ofNat 450, stack := stack} := by
  apply PadLift.gasSteps_of_raw prefixSite {s with pc := UInt256.ofNat 448, stack := stack} _ hcode hfork hrun hnp prefix_pc.symm prefix_advances
  have h1 : stack.length < 1024 := by omega
  have h : runInstrSeq prefixTemplate {s with pc := UInt256.ofNat 448, stack := stack} =
      some {s with pc := pcAfter (UInt256.ofNat 448) prefixTemplate, stack := stack} := by
    simp [prefixTemplate, runInstrSeq, Stepper.runInstr, if_pos h1, hrun]
    decide
  have hp : pcAfter (UInt256.ofNat 448) prefixTemplate = UInt256.ofNat 450 := by rfl
  rw [hp] at h
  exact h

#print axioms gasSteps_prefix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPadPrefix
