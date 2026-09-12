import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ConsumedTailTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TailMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TailSite
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace Table80ConsumedTerminalTail Paired80WordRound

theorem prefix_slice :
    (Artifact.submissionArtifact.instructions.drop 3902).take prefixTemplate.length =
      prefixTemplate := by rfl

def prefixSite : GenericRoundSite Artifact.submissionArtifact .Osaka prefixTemplate :=
  StackSiteBuilder.ofSlice prefixTemplate 3902 prefix_slice
    (by change 3902 + prefixTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := prefixTemplate) (by decide))
    (by decide)

theorem prefix_pc : prefixSite.startPC = UInt256.ofNat 4608 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3902) = UInt256.ofNat 4608
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem prefix_endPC : prefixSite.endPC = UInt256.ofNat 4707 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3973) = UInt256.ofNat 4707
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- The tail's stack cleanup ends at the post-check (pc 4707); there is no
return `JUMP`, the compressor falls through. -/
def gasSteps (s : State) (ret : UInt256) (q : WordLane) (factor : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4608, stack := entryStack factor q ret rho}
      {s with pc := UInt256.ofNat 4707, stack := ret :: rho, memory := resultMemory s.memory q} := by
  have g : GasSteps {s with pc := prefixSite.startPC, stack := entryStack factor q ret rho}
      {s with pc := prefixSite.endPC, stack := ret :: rho, memory := resultMemory s.memory q} :=
    Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka prefixSite.path hcode hfork
      (runLocatedBlock_tail_prefix prefixSite s ret q factor rho hstack hrun hactive) hrun hnp
  simpa only [prefix_pc, prefix_endPC] using g

#print axioms prefix_slice
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TailSite
