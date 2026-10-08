import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
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

/-- The `MSIZE` at 4569 (instruction 3428) that reads the pad-test bound. -/
theorem msize_decoded (s : State) (stack : List UInt256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka) :
    ({s with pc := UInt256.ofNat 4569, stack := stack} : State).decodedOp = some .MSIZE := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3428 .MSIZE
    (by rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of ({s with pc := UInt256.ofNat 4569, stack := stack} : State) 3428
    hcode ?_ .MSIZE none hd (by change Operation.MSIZE.availableInFork s.fork = true; rw [hfork]; rfl)
  change (UInt256.ofNat 4569).toNat = Artifact.submissionArtifact.instructionPC 3428
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

/-- `MSIZE` pushes the active memory size above the exit frame. -/
def gasSteps_msize (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4569, stack := exitFrame h off limit rho}
      {s with pc := UInt256.ofNat 4570, stack := UInt256.ofNat (32 * s.activeWords.toNat) :: exitFrame h off limit rho} := by
  have hcap : ({s with pc := UInt256.ofNat 4569, stack := exitFrame h off limit rho} : State).stack.length < 1024 := by
    change (exitFrame h off limit rho).length < 1024
    simp [exitFrame]; omega
  have g := Msize.step (msize_decoded s (exitFrame h off limit rho) hcode hfork) hcap hrun hnp
  exact g.cast rfl (by
    simp only [Word.succ_ofNat_mod])

def jumpCode : List Instr := PadJump.template 457
theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 3434).take jumpCode.length = jumpCode := by rfl
def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 3434 jump_slice
    (by change 3434 + jumpCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := jumpCode) (by decide)) (by decide)
theorem jump_pc : jumpSite.startPC = UInt256.ofNat 4576 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3434) = UInt256.ofNat 4576
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def swapCode : List Instr := StaggerPersistentLoopRaw.backTemplate

theorem swap_slice :
    (Artifact.submissionArtifact.instructions.drop 3433).take swapCode.length = swapCode := by rfl

def swapSite : GenericRoundSite Artifact.submissionArtifact .Osaka swapCode :=
  StackSiteBuilder.ofSlice swapCode 3433 swap_slice
    (by change 3433 + swapCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := swapCode) (by decide)) (by decide)

theorem swap_pc : swapSite.startPC = UInt256.ofNat 4575 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3433) = UInt256.ofNat 4575
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

/-- Pad test after the finish test failed: the offset differs from the active memory size. -/
def gasSteps_padMiss (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hmiss : off ≠ UInt256.ofNat (32 * s.activeWords.toNat))
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4569, stack := exitFrame h off limit rho}
      {s with pc := UInt256.ofNat 4575, stack := exitFrame h off limit rho} := by
  have g1 := gasSteps_msize s off limit h rho hstack hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 4570, stack := UInt256.ofNat (32 * s.activeWords.toNat) :: exitFrame h off limit rho}
      {s with pc := UInt256.ofNat 4575, stack := exitFrame h off limit rho} := by
    apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4570, stack := UInt256.ofNat (32 * s.activeWords.toNat) :: exitFrame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
    · exact PadLift.advancesAll_sound _ (by decide)
    · have hr := StaggerPersistentLoopRaw.run_miss s (UInt256.ofNat 4570) h off limit rho 129 (by omega) hrun
        _ hmiss
      have he : pcAfter (UInt256.ofNat 4570) (StaggerPersistentLoopRaw.padTemplate 129) = UInt256.ofNat 4575 := by decide
      rw [he] at hr
      exact hr
  exact g1.trans g2

/-- Pad test hit: jump to the pad-only block with the advanced offset still on top. -/
def gasSteps_padHit (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hhit : off = UInt256.ofNat (32 * s.activeWords.toNat))
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4569, stack := exitFrame h off limit rho}
      {s with pc := UInt256.ofNat 129, stack := exitFrame h off limit rho} := by
  have g1 := gasSteps_msize s off limit h rho hstack hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 4570, stack := UInt256.ofNat (32 * s.activeWords.toNat) :: exitFrame h off limit rho}
      {s with pc := UInt256.ofNat 129, stack := exitFrame h off limit rho} := by
    apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4570, stack := UInt256.ofNat (32 * s.activeWords.toNat) :: exitFrame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
    · exact PadLift.advancesAll_sound _ (by decide)
    · exact StaggerPersistentLoopRaw.run_hit s (UInt256.ofNat 4570) h off limit rho 129 (by omega) hrun
        _ hhit (valid_pad s hcode)
  exact g1.trans g2

/-- Neither finish nor pad: the advanced offset goes back into slot 12. -/
def gasSteps_swapBack (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4575, stack := exitFrame h off limit rho}
      {s with pc := UInt256.ofNat 4576, stack := frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw swapSite {s with pc := UInt256.ofNat 4575, stack := exitFrame h off limit rho} _ hcode hfork hrun hnp swap_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := StaggerPersistentLoopRaw.run_back s (UInt256.ofNat 4575) h off limit rho (by omega) hrun
    have he : pcAfter (UInt256.ofNat 4575) StaggerPersistentLoopRaw.backTemplate = UInt256.ofNat 4576 := by decide
    rw [he] at hr
    exact hr

/-- Neither finish nor pad: jump back to the loop head. -/
def gasSteps_back (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4576, stack := rho}
      {s with pc := UInt256.ofNat 457, stack := rho} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 4576, stack := rho} _ hcode hfork hrun hnp jump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template s (UInt256.ofNat 4576) rho 457 (by omega) hrun (valid_loop s hcode)

#print axioms gasSteps_padMiss
#print axioms gasSteps_padHit
#print axioms gasSteps_back
#print axioms gasSteps_swapBack
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
