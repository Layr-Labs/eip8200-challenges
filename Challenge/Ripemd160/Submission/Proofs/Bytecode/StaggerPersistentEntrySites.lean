import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentEntryRaw StaggerPersistentFrame PairedMask32Cache
def dispatchCode : List Instr := dispatchTemplate 4718
theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 3528).take dispatchCode.length = dispatchCode := by rfl
def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchCode :=
  StackSiteBuilder.ofSlice dispatchCode 3528 dispatch_slice
    (by change 3528 + dispatchCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchCode) (by decide)) (by decide)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 4655 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3528) = UInt256.ofNat 4655
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4718).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3576 = 4718 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3576 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 4718 = true
  rw [hcode]
  exact h

def gasSteps_hit (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hhit : s.executionEnv.calldata.size = off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4655, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 4718, stack := frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4655, stack := frame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := run_hit s (UInt256.ofNat 4655) off limit h rho 4718 hstack hrun hfit hhit (valid_pad s hcode)
    exact hr

def gasSteps_miss (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hmiss : s.executionEnv.calldata.size ≠ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4655, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 4662, stack := frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4655, stack := frame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := run_miss s (UInt256.ofNat 4655) off limit h rho 4718 hstack hrun hfit hmiss
    have he : pcAfter (UInt256.ofNat 4655) (dispatchTemplate 4718) = UInt256.ofNat 4662 := by decide
    rw [he] at hr
    exact hr

#print axioms gasSteps_miss
#print axioms gasSteps_hit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
