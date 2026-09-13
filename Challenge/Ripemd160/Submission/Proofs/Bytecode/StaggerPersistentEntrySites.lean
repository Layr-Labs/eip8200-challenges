import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentEntryRaw StaggerPersistentFrame
def dispatchCode : List Instr := dispatchTemplate 4773
theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 3713).take dispatchCode.length = dispatchCode := by rfl
def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchCode :=
  StackSiteBuilder.ofSlice dispatchCode 3713 dispatch_slice
    (by change 3713 + dispatchCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchCode) (by decide)) (by decide)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 4632 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3713) = UInt256.ofNat 4632
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def callCode : List Instr := callTemplate
theorem call_slice :
    (Artifact.submissionArtifact.instructions.drop 270).take callCode.length = callCode := by rfl
def callSite : GenericRoundSite Artifact.submissionArtifact .Osaka callCode :=
  StackSiteBuilder.ofSlice callCode 270 call_slice
    (by change 270 + callCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := callCode) (by decide)) (by decide)
theorem call_pc : callSite.startPC = UInt256.ofNat 484 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 270) = UInt256.ofNat 484
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4773).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3791 = 4773 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3791 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 4773 = true
  rw [hcode]
  exact h

def gasSteps_hit (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hhit : s.executionEnv.calldata.size = off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4632, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 4773, stack := frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4632, stack := frame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := run_hit s (UInt256.ofNat 4632) off limit h rho 4773 hstack hrun hfit hhit (valid_pad s hcode)
    exact hr

def gasSteps_miss (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hmiss : s.executionEnv.calldata.size ≠ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4632, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 4639, stack := frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4632, stack := frame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := run_miss s (UInt256.ofNat 4632) off limit h rho 4773 hstack hrun hfit hmiss
    have he : pcAfter (UInt256.ofNat 4632) (dispatchTemplate 4773) = UInt256.ofNat 4639 := by decide
    rw [he] at hr
    exact hr

def gasSteps_call (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 484, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 489, stack := pointer off :: frame h off limit rho} := by
  apply DenseScheduleLift.gasSteps_of_raw callSite {s with pc := UInt256.ofNat 484, stack := frame h off limit rho} _ hcode hfork hrun hnp call_pc.symm
  · exact Table80SiteCommon.coreAdvancesAll_sound _ (by decide)
  · have hr := run_call s (UInt256.ofNat 484) off limit h rho hstack hrun
    have he : pcAfter (UInt256.ofNat 484) callTemplate = UInt256.ofNat 489 := by decide
    rw [he] at hr
    exact hr
#print axioms gasSteps_call
#print axioms gasSteps_miss
#print axioms gasSteps_hit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
