import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentEntryRaw StaggerPersistentFrame PairedMask32Cache
def dispatchCode : List Instr := StaggerPersistentLoopRaw.padTemplate 129
theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 3429).take dispatchCode.length = dispatchCode := by rfl
def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchCode :=
  StackSiteBuilder.ofSlice dispatchCode 3429 dispatch_slice
    (by change 3429 + dispatchCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchCode) (by decide)) (by decide)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 4570 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3429) = UInt256.ofNat 4570
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def jumpCode : List Instr := PadJump.template 457
theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 3435).take jumpCode.length = jumpCode := by rfl
def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 3435 jump_slice
    (by change 3435 + jumpCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := jumpCode) (by decide)) (by decide)
theorem jump_pc : jumpSite.startPC = UInt256.ofNat 4577 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3435) = UInt256.ofNat 4577
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_finish (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4581).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3437 = 4581 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3437 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 4581 = true
  rw [hcode]
  exact h

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 129).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 80 = 129 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 80 (by rfl)
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

/-- Pad test after the finish test failed: the offset differs from the limit. -/
def gasSteps_padMiss (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hmiss : off ≠ limit)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4570, stack := exitFrame h off limit rho}
      {s with pc := UInt256.ofNat 4577, stack := frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4570, stack := exitFrame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := StaggerPersistentLoopRaw.run_miss s (UInt256.ofNat 4570) h off limit rho 129 (by omega) hrun hmiss
    have he : pcAfter (UInt256.ofNat 4570) (StaggerPersistentLoopRaw.padTemplate 129) = UInt256.ofNat 4577 := by decide
    rw [he] at hr
    exact hr

/-- Pad test hit: jump to the pad-only block setup. -/
def gasSteps_padHit (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hhit : off = limit)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4570, stack := exitFrame h off limit rho}
      {s with pc := UInt256.ofNat 129, stack := frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4570, stack := exitFrame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · exact StaggerPersistentLoopRaw.run_hit s (UInt256.ofNat 4570) h off limit rho 129 (by omega) hrun hhit
      (valid_pad s hcode)

/-- Neither finish nor pad: jump back to the loop head. -/
def gasSteps_back (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4577, stack := rho}
      {s with pc := UInt256.ofNat 457, stack := rho} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 4577, stack := rho} _ hcode hfork hrun hnp jump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template s (UInt256.ofNat 4577) rho 457 (by omega) hrun (valid_loop s hcode)

#print axioms gasSteps_padMiss
#print axioms gasSteps_padHit
#print axioms gasSteps_back
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
