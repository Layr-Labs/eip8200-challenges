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
    (Artifact.submissionArtifact.instructions.drop 3917).take prefixTemplate.length =
      prefixTemplate := by rfl

def prefixSite : GenericRoundSite Artifact.submissionArtifact .Osaka prefixTemplate :=
  StackSiteBuilder.ofSlice prefixTemplate 3917 prefix_slice
    (by change 3917 + prefixTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := prefixTemplate) (by decide))
    (by decide)

theorem prefix_pc : prefixSite.startPC = UInt256.ofNat 4615 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3917) = UInt256.ofNat 4615
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem prefix_endPC : prefixSite.endPC = UInt256.ofNat 4717 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3993) = UInt256.ofNat 4717
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def jumpSite : LocatedSite Artifact.submissionArtifact .Osaka where
  located := {
    index := 3993
    instruction := .op .JUMP
    atIndex := by rfl
    wellFormed := StackRoundData.templateWellFormed_mem
      (instructions := [.op .JUMP]) (by decide) _ (by simp) }
  pc := UInt256.ofNat 4717
  pc_eq := by
    change (UInt256.ofNat 4717).toNat = Artifact.submissionArtifact.instructionPC 3993
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def site : TailSite Artifact.submissionArtifact .Osaka where
  prefixSite := prefixSite
  jump := jumpSite
  jump_instr := rfl
  jump_pc := prefix_endPC.symm

def gasSteps (s : State) (ret : UInt256) (q : WordLane) (factor : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4615, stack := entryStack factor q ret rho}
      {s with pc := ret, stack := rho, memory := resultMemory s.memory q} := by
  have g := gasSteps_tail site s ret q factor rho hstack hrun hactive hvalid hcode hfork hnp
  change GasSteps {s with pc := prefixSite.startPC, stack := entryStack factor q ret rho}
    {s with pc := ret, stack := rho, memory := resultMemory s.memory q} at g
  simpa only [prefix_pc] using g

#print axioms prefix_slice
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TailSite
