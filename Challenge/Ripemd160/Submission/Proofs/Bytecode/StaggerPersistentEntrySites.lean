import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentEntryRaw StaggerPersistentFrame PairedMask32Cache
def dispatchCode : List Instr := dispatchTemplate 4740
theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 3679).take dispatchCode.length = dispatchCode := by rfl
def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchCode :=
  StackSiteBuilder.ofSlice dispatchCode 3679 dispatch_slice
    (by change 3679 + dispatchCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchCode) (by decide)) (by decide)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 4599 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3679) = UInt256.ofNat 4599
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def callCode : List Instr := callTemplate
theorem call_slice :
    (Artifact.submissionArtifact.instructions.drop 276).take callCode.length = callCode := by rfl
def callSite : GenericRoundSite Artifact.submissionArtifact .Osaka callCode :=
  StackSiteBuilder.ofSlice callCode 276 call_slice
    (by change 276 + callCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := callCode) (by decide)) (by decide)
theorem call_pc : callSite.startPC = UInt256.ofNat 491 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 276) = UInt256.ofNat 491
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4740).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3757 = 4740 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3757 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 4740 = true
  rw [hcode]
  exact h

def gasSteps_hit (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hhit : s.executionEnv.calldata.size = off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4599, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 4740, stack := frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4599, stack := frame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := run_hit s (UInt256.ofNat 4599) off limit h rho 4740 hstack hrun hfit hhit (valid_pad s hcode)
    exact hr

def gasSteps_miss (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hmiss : s.executionEnv.calldata.size ≠ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4599, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 4606, stack := frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4599, stack := frame h off limit rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := run_miss s (UInt256.ofNat 4599) off limit h rho 4740 hstack hrun hfit hmiss
    have he : pcAfter (UInt256.ofNat 4599) (dispatchTemplate 4740) = UInt256.ofNat 4606 := by decide
    rw [he] at hr
    exact hr

private def callAdvancesCheck : Instr → Bool
  | .op .DIV => true
  | instruction => PadLift.advancesCheck instruction

private theorem callAdvancesCheck_sound (instruction : Instr) (h : callAdvancesCheck instruction = true)
    {s t : State} (hresult : DataStepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  cases instruction with
  | push width value =>
    exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ h) hresult
  | op operation =>
    cases operation <;> first
      | exact PairedDivMaskCache.runInstr_pc_div hresult
      | exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ h) hresult
      | (rename_i inner; cases inner <;> first
          | exact PairedDivMaskCache.runInstr_pc_div hresult
          | exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ h) hresult)

private theorem call_advances (instruction : Instr)
    (hi : instruction ∈ callTemplate.dropLast) {s t : State}
    (hr : DataStepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  have hall : callTemplate.dropLast.all callAdvancesCheck = true := by decide
  exact callAdvancesCheck_sound instruction ((List.all_eq_true.mp hall) instruction hi) hr

private def call_gasSteps_of_raw (s t : State)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hpc : s.pc = callSite.startPC)
    (hresult : runInstrSeq callTemplate s = some t) : GasSteps s t := by
  apply DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka callSite.path hcode hfork
  · have hl := PairedHelperBooleanTrace.runLocatedBlock_eq_raw_terminal_sites callSite.sites callTemplate
      callSite.instruction_eq callSite.contiguous s
      (by rw [callSite.head_eq]; exact congrArg some hpc.symm) (by
        intro located hmem u v hr
        apply call_advances _ ?_ hr
        have hm : located.located.instruction ∈
            callSite.sites.dropLast.map (fun item => item.located.instruction) := List.mem_map_of_mem hmem
        rw [List.map_dropLast, callSite.instruction_eq] at hm
        exact hm)
    change DataStepper.runLocatedBlock (LocatedSite.path callSite.sites) s = some t
    rw [hl]
    exact hresult
  · exact hrun
  · exact hnp

def gasSteps_call (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 491, stack := frame h off limit rho}
      {s with pc := UInt256.ofNat 509, stack := pointer off :: DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: frame h off limit rho} := by
  apply call_gasSteps_of_raw {s with pc := UInt256.ofNat 491, stack := frame h off limit rho} _ hcode hfork hrun hnp call_pc.symm
  have hr := run_call s (UInt256.ofNat 491) off limit h rho hstack hrun
  have he : pcAfter (UInt256.ofNat 491) callTemplate = UInt256.ofNat 509 := by decide
  rw [he] at hr
  exact hr
#print axioms gasSteps_call
#print axioms gasSteps_miss
#print axioms gasSteps_hit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
