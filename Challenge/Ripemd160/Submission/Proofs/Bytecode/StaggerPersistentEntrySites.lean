import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentEntryRaw StaggerPersistentFrame PairedMask32Cache
def dispatchCode : List Instr := dispatchTemplate 457
theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 3430).take dispatchCode.length = dispatchCode := by rfl
def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchCode :=
  StackSiteBuilder.ofSlice dispatchCode 3430 dispatch_slice
    (by change 3430 + dispatchCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchCode) (by decide)) (by decide)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 4570 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3430) = UInt256.ofNat 4570
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 129).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 79 = 129 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 79 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 129 = true
  rw [hcode]
  exact h

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 457).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 174 = 457 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 174 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 457 = true
  rw [hcode]
  exact h

/-- Second test after a block (the offset differs from the limit): more whole blocks. -/
def gasSteps_lt (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hlt : off.toNat < limit.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4570, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 457, stack := frame h off limit rho} := by
  apply RecognitionLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4570, stack := frame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact RecognitionLift.advancesAll_sound _ (by decide)
  · have hr := run_lt s (UInt256.ofNat 4570) off limit h rho 457 hstack hrun hlt (valid_loop s hcode)
    exact hr

/-- Second test after a block: the offset is past the limit, fall through to the output. -/
def gasSteps_ge (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hge : limit.toNat ≤ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4570, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 4577, stack := frame h off limit rho} := by
  apply RecognitionLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4570, stack := frame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact RecognitionLift.advancesAll_sound _ (by decide)
  · have hr := run_ge s (UInt256.ofNat 4570) off limit h rho 457 hstack hrun hge
    have he : pcAfter (UInt256.ofNat 4570) (dispatchTemplate 457) = UInt256.ofNat 4577 := by decide
    rw [he] at hr
    exact hr

#print axioms gasSteps_lt
#print axioms gasSteps_ge
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
