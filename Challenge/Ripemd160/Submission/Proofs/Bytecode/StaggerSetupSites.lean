import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80NoJumpdest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerNormalSchedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPadSetup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerSetupSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace Table80Setup
open StaggerPad (run_pad)

def actualNormalTemplate : List Instr := StaggerNormal.normalTemplate.tail

theorem normal_slice :
    (Artifact.submissionArtifact.instructions.drop 314).take actualNormalTemplate.length = actualNormalTemplate := by rfl

def normalSite : GenericRoundSite Artifact.submissionArtifact .Osaka actualNormalTemplate :=
  StackSiteBuilder.ofSlice actualNormalTemplate 314 normal_slice
    (by change 314 + actualNormalTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := actualNormalTemplate) (by decide))
    (by decide)
theorem normal_pc : normalSite.startPC = UInt256.ofNat 510 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 314) = UInt256.ofNat 510
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private def advancesCheck : Instr → Bool
  | .op .DIV => true
  | instruction => PadLift.advancesCheck instruction

private theorem advancesCheck_sound (instruction : Instr) (h : advancesCheck instruction = true)
    {s t : State} (hresult : Stepper.runInstr instruction s = some t) :
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

theorem normal_advances : ∀ instruction ∈ actualNormalTemplate.dropLast, ∀ {s t : State},
    Stepper.runInstr instruction s = some t → t.pc = s.pc + UInt256.ofNat instruction.size := by
  have hall : actualNormalTemplate.dropLast.all advancesCheck = true := by decide
  intro instruction hi s t hr
  exact advancesCheck_sound instruction ((List.all_eq_true.mp hall) instruction hi) hr

private def normal_gasSteps_of_raw (s t : State)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hpc : s.pc = normalSite.startPC)
    (hresult : runInstrSeq actualNormalTemplate s = some t) : GasSteps s t := by
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka normalSite.path hcode hfork
  · have hl := runLocatedBlock_eq_raw_terminal_sites normalSite.sites actualNormalTemplate
      normalSite.instruction_eq normalSite.contiguous s
      (by rw [normalSite.head_eq]; exact congrArg some hpc.symm) (by
        intro located hmem u v hr
        apply normal_advances _ ?_ hr
        have hm : located.located.instruction ∈
            normalSite.sites.dropLast.map (fun item => item.located.instruction) := List.mem_map_of_mem hmem
        rw [List.map_dropLast, normalSite.instruction_eq] at hm
        exact hm)
    change Stepper.runLocatedBlock (LocatedSite.path normalSite.sites) s = some t
    rw [hl]
    exact hresult
  · exact hrun
  · exact hnp

theorem normal_end : pcAfter (UInt256.ofNat 510) actualNormalTemplate = UInt256.ofNat 940 := by decide

theorem pad_slice :
    (Artifact.submissionArtifact.instructions.drop 248).take StaggerPad.padTemplate.length = StaggerPad.padTemplate := by rfl

def padSite : GenericRoundSite Artifact.submissionArtifact .Osaka StaggerPad.padTemplate :=
  StackSiteBuilder.ofSlice StaggerPad.padTemplate 248 pad_slice
    (by change 248 + StaggerPad.padTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := StaggerPad.padTemplate) (by decide))
    (by decide)
theorem pad_pc : padSite.startPC = UInt256.ofNat 406 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 248) = UInt256.ofNat 406
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem pad_advances : ∀ instruction ∈ StaggerPad.padTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem pad_end : pcAfter (UInt256.ofNat 406) StaggerPad.padTemplate = UInt256.ofNat 479 := by decide

def gasSteps_normal (s : State) (ret : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 896) (hrun : s.halt = .Running)
    (hp : 1024 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 510, stack := UInt256.ofNat p :: ret :: rest}
      {s with pc := UInt256.ofNat 940, stack := ret :: rest, memory := StaggerTableLayout.resultMemory s.memory (PairedScheduleData.extractedWord s.memory p), activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p)} := by
  apply normal_gasSteps_of_raw {s with pc := UInt256.ofNat 510, stack := UInt256.ofNat p :: ret :: rest} _ hcode hfork hrun hnp normal_pc.symm
  have h := StaggerNormal.run_normal s (UInt256.ofNat 509) ret p rest hstack hrun hp hbound
  have hfull : StaggerNormal.normalTemplate = .op .JUMPDEST :: actualNormalTemplate := by rfl
  have hend : pcAfter (UInt256.ofNat 509) StaggerNormal.normalTemplate = UInt256.ofNat 940 := by decide
  rw [hend, hfull] at h
  have ht := run_without_jumpdest actualNormalTemplate
    (DenseScheduleTemplate.scheduleEntry s (UInt256.ofNat 509) (UInt256.ofNat p) ret rest) _ (by decide)
    (by simp only [DenseScheduleTemplate.scheduleEntry, List.length_append, List.length_cons, List.length_nil]; omega) hrun h
  simpa only [DenseScheduleTemplate.scheduleEntry, List.cons_append, List.nil_append, show (UInt256.ofNat 509).succ = UInt256.ofNat 510 by decide] using ht

def gasSteps_pad (s : State) (ret : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 896) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 406, stack := ret :: rest}
      {s with pc := UInt256.ofNat 479, stack := ret :: rest, memory := StaggerTablePad.resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  apply PadLift.gasSteps_of_raw padSite {s with pc := UInt256.ofNat 406, stack := ret :: rest} _ hcode hfork hrun hnp pad_pc.symm pad_advances
  have h := StaggerPad.run_pad s (UInt256.ofNat 406) ret rest (by omega) hrun hactive hfit
  rw [pad_end] at h
  exact h
#print axioms gasSteps_normal
#print axioms gasSteps_pad
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerSetupSites
