import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Lower
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Physical
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
abbrev sourceTemplate := Source32Lower.sourceTemplate

theorem source_slice :
    (Artifact.submissionArtifact.instructions.drop 322).take sourceTemplate.length = sourceTemplate := by rfl

def sourceSite : GenericRoundSite Artifact.submissionArtifact .Osaka sourceTemplate :=
  StackSiteBuilder.ofSlice sourceTemplate 322 source_slice
    (by change 322 + sourceTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := sourceTemplate) (by decide)) (by decide)

theorem source_pc : sourceSite.startPC = UInt256.ofNat 525 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 322) = UInt256.ofNat 525
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private def advancesCheck : Instr → Bool
  | .op .DIV => true
  | instruction => PadLift.advancesCheck instruction

private theorem advancesCheck_sound (instruction : Instr) (h : advancesCheck instruction = true)
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

theorem source_advances : ∀ instruction ∈ sourceTemplate.dropLast, ∀ {s t : State},
    DataStepper.runInstr instruction s = some t → t.pc = s.pc + UInt256.ofNat instruction.size := by
  have hall : sourceTemplate.dropLast.all advancesCheck = true := by decide
  intro instruction hi s t hr
  exact advancesCheck_sound instruction ((List.all_eq_true.mp hall) instruction hi) hr

private def source_gasSteps_of_raw (s t : State)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hpc : s.pc = sourceSite.startPC)
    (hresult : runInstrSeq sourceTemplate s = some t) : GasSteps s t := by
  apply DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka sourceSite.path hcode hfork
  · have hl := runLocatedBlock_eq_raw_terminal_sites sourceSite.sites sourceTemplate
      sourceSite.instruction_eq sourceSite.contiguous s
      (by rw [sourceSite.head_eq]; exact congrArg some hpc.symm) (by
        intro located hmem u v hr
        apply source_advances _ ?_ hr
        have hm : located.located.instruction ∈
            sourceSite.sites.dropLast.map (fun item => item.located.instruction) := List.mem_map_of_mem hmem
        rw [List.map_dropLast, sourceSite.instruction_eq] at hm
        exact hm)
    change DataStepper.runLocatedBlock (LocatedSite.path sourceSite.sites) s = some t
    rw [hl]
    exact hresult
  · exact hrun
  · exact hnp

theorem source_end : pcAfter (UInt256.ofNat 525) sourceTemplate = UInt256.ofNat 909 := by decide

def resultMemory (memory : ByteArray) : ByteArray :=
  StaggerTableLayout.resultMemory (Source32Lower.lowerScratch memory 1120)
    (StaggerScratch.poolWordD (Source32Lower.lowerScratch memory 1120))

def gasSteps_source (s : State) (h : Compression.HashState) (limit : UInt256)
    (hrun : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hactive : DenseScheduleTemplate.activeAfterWord s.activeWords (UInt256.ofNat 1120) = s.activeWords)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with
      pc := UInt256.ofNat 525
      stack := StaggerPersistentFrame.frame h (UInt256.ofNat 0) limit
        [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]}
      {s with
        pc := UInt256.ofNat 909
        stack := StaggerPersistentFrame.frame h (UInt256.ofNat 0) limit
          [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
        memory := resultMemory s.memory} := by
  apply source_gasSteps_of_raw
    {s with pc := UInt256.ofNat 525, stack := StaggerPersistentFrame.frame h (UInt256.ofNat 0) limit [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]}
    _ hcode hfork hrun hnp source_pc.symm
  have hr := Source32Lower.run_source s (UInt256.ofNat 525)
    Paired144WordRound.factorPlusWord
    (Paired144WordRound.fusedModulusWord 5 7) (Paired144WordRound.fusedModulusWord 8 5)
    (Paired144WordRound.fusedCoefficientWord 0 3) (Paired144WordRound.fusedCoefficientWord 0 2)
    (Word.ofUInt32 h.h4) (Word.ofUInt32 h.h1) (Word.ofUInt32 h.h2)
    (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h0) (UInt256.ofNat 0) limit [] 1120
    (by decide) hrun ha (by decide) (by decide) hactive
  rw [source_end] at hr
  simpa only [resultMemory, StaggerPersistentFrame.frame, PersistentMaskEndian.stk,
    List.cons_append, List.nil_append] using hr
#print axioms gasSteps_source
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Physical
