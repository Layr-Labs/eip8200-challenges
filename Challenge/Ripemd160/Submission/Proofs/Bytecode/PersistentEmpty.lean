import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentReturn
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptySpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentEmpty
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

def digest : UInt256 := UInt256.ofNat EmptySpec.digestNat
def pushTemplate : List Instr := [.push ⟨20, by decide⟩ digest]

theorem push_slice :
    (Artifact.submissionArtifact.instructions.drop 229).take pushTemplate.length = pushTemplate := by rfl

def pushSite : GenericRoundSite Artifact.submissionArtifact .Osaka pushTemplate :=
  StackSiteBuilder.ofSlice pushTemplate 229 push_slice
    (by change 229 + pushTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    Artifact.code_size_lt
    (StackRoundData.templateWellFormed_mem (instructions := pushTemplate) (by decide))
    (by decide)

theorem push_pc : pushSite.startPC = UInt256.ofNat 365 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 229) = UInt256.ofNat 365
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem return_slice :
    (Artifact.submissionArtifact.instructions.drop 230).take PersistentReturn.template.length =
      PersistentReturn.template := by rfl

def returnSite : GenericRoundSite Artifact.submissionArtifact .Osaka PersistentReturn.template :=
  StackSiteBuilder.ofSlice PersistentReturn.template 230 return_slice
    (by change 230 + PersistentReturn.template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    Artifact.code_size_lt
    (StackRoundData.templateWellFormed_mem (instructions := PersistentReturn.template) (by decide))
    (by decide)

theorem return_pc : returnSite.startPC = UInt256.ofNat 386 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 230) = UInt256.ofNat 386
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def result (s : State) (rho : List UInt256) : State :=
  PersistentReturn.result s (UInt256.ofNat 386) digest rho

def gasSteps_return (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1019) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 365, stack := rho} (result s rho) := by
  have gp : GasSteps {s with pc := UInt256.ofNat 365, stack := rho}
      {s with pc := UInt256.ofNat 386, stack := digest :: rho} := by
    apply PadLift.gasSteps_of_raw pushSite {s with pc := UInt256.ofNat 365, stack := rho} _
      hcode hfork hrun hnp push_pc.symm
    · apply PadLift.advancesAll_sound
      decide
    · have hs : rho.length < 1024 := by omega
      simp [pushTemplate, runInstrSeq, Stepper.runInstr, hrun, hs]
      rfl
  have gr := PersistentReturn.gasSteps_site returnSite s digest rho hstack hcode hfork hrun hnp
  rw [return_pc] at gr
  exact gp.trans gr

def gasSteps_empty (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 365, stack := PersistentFrame.frame h off limit rho}
      (result s (PersistentFrame.frame h off limit rho)) :=
  gasSteps_return s _ (by simp [PersistentFrame.frame]; omega) hrun hcode hfork hnp

theorem returned_bytes (s : State) (rho : List UInt256) :
    (result s rho).hReturn = Challenge.Ripemd160.spec ByteArray.empty := by
  rw [EmptySpec.spec_empty]
  unfold result
  rw [PersistentReturn.returned_bytes]
  change Data.Bytes.natToBytesPadded (UInt256.ofNat EmptySpec.digestNat).toNat 32 = EmptySpec.emptyOutput
  rw [Memory.natToBytesPadded_eq_natToBE]
  decide

theorem returned (s : State) (rho : List UInt256) : (result s rho).halt = .Returned := rfl

#print axioms gasSteps_empty
#print axioms returned_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentEmpty
