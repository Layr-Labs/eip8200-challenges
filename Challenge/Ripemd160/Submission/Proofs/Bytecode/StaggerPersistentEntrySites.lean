import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentEntryRaw StaggerPersistentFrame
def callCode : List Instr := callTemplate
theorem call_slice :
    (Artifact.submissionArtifact.instructions.drop 336).take callCode.length = callCode := by rfl
def callSite : GenericRoundSite Artifact.submissionArtifact .Osaka callCode :=
  StackSiteBuilder.ofSlice callCode 336 call_slice
    (by change 336 + callCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := callCode) (by decide)) (by decide)
theorem call_pc : callSite.startPC = UInt256.ofNat 528 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 336) = UInt256.ofNat 528
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
def dispatchCode : List Instr := dispatchTemplate 448
theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 339).take dispatchCode.length = dispatchCode := by rfl
def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchCode :=
  StackSiteBuilder.ofSlice dispatchCode 339 dispatch_slice
    (by change 339 + dispatchCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchCode) (by decide)) (by decide)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 533 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 339) = UInt256.ofNat 533
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 448).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 285 = 448 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 285 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 448 = true
  rw [hcode]
  exact h
def gasSteps_call (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 528, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 533, stack := pointer off :: frame h off limit rho} := by
  apply DenseScheduleLift.gasSteps_of_raw callSite {s with pc := UInt256.ofNat 528, stack := frame h off limit rho} _ hcode hfork hrun hnp call_pc.symm
  · exact Table80SiteCommon.coreAdvancesAll_sound _ (by decide)
  · have hr := run_call s (UInt256.ofNat 528) off limit h rho hstack hrun
    have he : pcAfter (UInt256.ofNat 528) callTemplate = UInt256.ofNat 533 := by decide
    rw [he] at hr
    exact hr
def gasSteps_miss (s : State) (ptr off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hmiss : s.executionEnv.calldata.size ≠ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 533, stack := ptr :: frame h off limit rho}
      {s with pc := UInt256.ofNat 540, stack := ptr :: frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 533, stack := ptr :: frame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := run_miss s (UInt256.ofNat 533) ptr off limit h rho 448 hstack hrun hfit hmiss
    have he : pcAfter (UInt256.ofNat 533) (dispatchTemplate 448) = UInt256.ofNat 540 := by decide
    rw [he] at hr
    exact hr
def gasSteps_hit (s : State) (ptr off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hhit : s.executionEnv.calldata.size = off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 533, stack := ptr :: frame h off limit rho}
      {s with pc := UInt256.ofNat 448, stack := ptr :: frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 533, stack := ptr :: frame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := run_hit s (UInt256.ofNat 533) ptr off limit h rho 448 hstack hrun hfit hhit (valid_pad s hcode)
    exact hr
#print axioms gasSteps_call
#print axioms gasSteps_miss
#print axioms gasSteps_hit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
