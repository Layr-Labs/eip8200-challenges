import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPadPrefix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate
def prefixTemplate : List Instr := [.op .JUMPDEST, .op .POP]
theorem prefix_slice :
    (Artifact.submissionArtifact.instructions.drop 236).take prefixTemplate.length = prefixTemplate := by rfl
def prefixSite : GenericRoundSite Artifact.submissionArtifact .Osaka prefixTemplate :=
  StackSiteBuilder.ofSlice prefixTemplate 236 prefix_slice
    (by change 236 + prefixTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := prefixTemplate) (by decide))
    (by decide)
theorem prefix_pc : prefixSite.startPC = UInt256.ofNat 392 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 236) = UInt256.ofNat 392
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem prefix_advances : ∀ instruction ∈ prefixTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

def gasSteps_prefix (s : State) (ret : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 1019) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 392, stack := UInt256.ofNat p :: ret :: rest}
      {s with pc := UInt256.ofNat 394, stack := ret :: rest} := by
  apply PadLift.gasSteps_of_raw prefixSite {s with pc := UInt256.ofNat 392, stack := UInt256.ofNat p :: ret :: rest} _ hcode hfork hrun hnp prefix_pc.symm prefix_advances
  have h : runInstrSeq prefixTemplate {s with pc := UInt256.ofNat 392, stack := UInt256.ofNat p :: ret :: rest} =
      some {s with pc := pcAfter (UInt256.ofNat 392) prefixTemplate, stack := ret :: rest} := by
    have hcap (n : Nat) (hn : n ≤ 4) : rest.length + n < 1024 := by omega
    simp (discharger := omega) [prefixTemplate, runInstrSeq, Stepper.runInstr, pcAfter,
      UInt256.succ, Instr.size, hrun, hcap, List.length_cons, Nat.add_assoc]
    rfl
  have hp : pcAfter (UInt256.ofNat 392) (prefixTemplate) = UInt256.ofNat 394 := by rfl
  rw [hp] at h
  exact h

#print axioms gasSteps_prefix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPadPrefix
