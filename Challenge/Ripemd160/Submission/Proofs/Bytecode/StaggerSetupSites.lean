import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80NoJumpdest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalSchedule
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

def actualNormalTemplate : List Instr := DeferredNormalSchedule.normalTemplate

theorem normal_slice :
    (Artifact.submissionArtifact.instructions.drop 295).take actualNormalTemplate.length = actualNormalTemplate := by rfl

def normalSite : GenericRoundSite Artifact.submissionArtifact .Osaka actualNormalTemplate :=
  StackSiteBuilder.ofSlice actualNormalTemplate 295 normal_slice
    (by change 295 + actualNormalTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := actualNormalTemplate) (by decide))
    (by decide)
theorem normal_pc : normalSite.startPC = UInt256.ofNat 488 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 295) = UInt256.ofNat 488
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

theorem normal_advances : ∀ instruction ∈ actualNormalTemplate.dropLast, ∀ {s t : State},
    DataStepper.runInstr instruction s = some t → t.pc = s.pc + UInt256.ofNat instruction.size := by
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
  apply DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka normalSite.path hcode hfork
  · have hl := runLocatedBlock_eq_raw_terminal_sites normalSite.sites actualNormalTemplate
      normalSite.instruction_eq normalSite.contiguous s
      (by rw [normalSite.head_eq]; exact congrArg some hpc.symm) (by
        intro located hmem u v hr
        apply normal_advances _ ?_ hr
        have hm : located.located.instruction ∈
            normalSite.sites.dropLast.map (fun item => item.located.instruction) := List.mem_map_of_mem hmem
        rw [List.map_dropLast, normalSite.instruction_eq] at hm
        exact hm)
    change DataStepper.runLocatedBlock (LocatedSite.path normalSite.sites) s = some t
    rw [hl]
    exact hresult
  · exact hrun
  · exact hnp

theorem normal_end : pcAfter (UInt256.ofNat 488) actualNormalTemplate = UInt256.ofNat 904 := by decide

theorem low_slice :
    (Artifact.submissionArtifact.instructions.drop 3720).take StaggerPad.lowTemplate.length = StaggerPad.lowTemplate := by rfl

def lowSite : GenericRoundSite Artifact.submissionArtifact .Osaka StaggerPad.lowTemplate :=
  StackSiteBuilder.ofSlice StaggerPad.lowTemplate 3720 low_slice
    (by change 3720 + StaggerPad.lowTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := StaggerPad.lowTemplate) (by decide))
    (by decide)
theorem low_pc : lowSite.startPC = UInt256.ofNat 4763 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3720) = UInt256.ofNat 4763
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem low_advances : ∀ instruction ∈ StaggerPad.lowTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem low_end : pcAfter (UInt256.ofNat 4763) StaggerPad.lowTemplate = UInt256.ofNat 4804 := by decide

open StaggerPad (branchTemplate)

theorem branch_slice :
    (Artifact.submissionArtifact.instructions.drop 3748).take branchTemplate.length = branchTemplate := by rfl

def branchSite : GenericRoundSite Artifact.submissionArtifact .Osaka branchTemplate :=
  StackSiteBuilder.ofSlice branchTemplate 3748 branch_slice
    (by change 3748 + branchTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := branchTemplate) (by decide))
    (by decide)
theorem branch_pc : branchSite.startPC = UInt256.ofNat 4804 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3748) = UInt256.ofNat 4804
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem branch_advances : ∀ instruction ∈ branchTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem branch_end : pcAfter (UInt256.ofNat 4804) branchTemplate = UInt256.ofNat 4808 := by decide

theorem high_slice :
    (Artifact.submissionArtifact.instructions.drop 3750).take StaggerPad.highTemplate.length = StaggerPad.highTemplate := by rfl

def highSite : GenericRoundSite Artifact.submissionArtifact .Osaka StaggerPad.highTemplate :=
  StackSiteBuilder.ofSlice StaggerPad.highTemplate 3750 high_slice
    (by change 3750 + StaggerPad.highTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := StaggerPad.highTemplate) (by decide))
    (by decide)
theorem high_pc : highSite.startPC = UInt256.ofNat 4808 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3750) = UInt256.ofNat 4808
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem high_advances : ∀ instruction ∈ StaggerPad.highTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem high_end : pcAfter (UInt256.ofNat 4808) StaggerPad.highTemplate = UInt256.ofNat 4836 := by decide

theorem valid_rounds (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 904).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 572 = 904 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 572 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 904 = true
  rw [hcode]
  exact h

def gasSteps_normal (s : State) (ret : UInt256) (p : Nat) (rest : List UInt256)
    (hmask : rest.head? = some PairedMask32Cache.maskWord)
    (hoff : rest[10]? = some (UInt256.ofNat (p - 1120)))
    (hstack : rest.length ≤ 896) (hrun : s.halt = .Running)
    (hp : 1120 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hlow : (MachineState.readWord s.memory 0).toNat < 2 ^ 32)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 488, stack := UInt256.ofNat p :: DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: ret :: rest}
      {s with pc := UInt256.ofNat 904, stack := ret :: rest, memory := StaggerTableLayout.resultMemory s.memory (StaggerScratch.dirtyWord s.memory p), activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p)} := by
  cases rest with
  | nil => simp at hmask
  | cons mask tailRest =>
    simp only [List.head?_cons, Option.some.injEq] at hmask
    subst mask
    simp only [List.length_cons] at hstack
    apply normal_gasSteps_of_raw {s with pc := UInt256.ofNat 488, stack := UInt256.ofNat p :: DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: ret :: PairedMask32Cache.maskWord :: tailRest} _ hcode hfork hrun hnp normal_pc.symm
    have h := DeferredNormalSchedule.run_normal s (UInt256.ofNat 488) ret p tailRest (by omega) hrun hp hbound hlow hoff
    have hend : pcAfter (UInt256.ofNat 488) DeferredNormalSchedule.normalTemplate = UInt256.ofNat 904 := by decide
    rw [hend] at h
    exact h

def gasSteps_low (s : State) (ret : UInt256) (rest : List UInt256)
    (hmask : rest.head? = some (UInt256.ofNat 4294967295))
    (hstack : rest.length ≤ 896) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4763, stack := ret :: rest}
      {s with
        pc := UInt256.ofNat 4804
        stack := StaggerPad.highZero (UInt256.ofNat s.executionEnv.calldata.size) :: ret :: rest
        memory := StaggerTablePad.lowChain s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  cases rest with
  | nil => simp at hmask
  | cons mask tailRest =>
    simp only [List.head?_cons, Option.some.injEq] at hmask
    subst mask
    simp only [List.length_cons] at hstack
    apply PadLift.gasSteps_of_raw lowSite {s with pc := UInt256.ofNat 4763, stack := ret :: UInt256.ofNat 4294967295 :: tailRest} _ hcode hfork hrun hnp low_pc.symm low_advances
    have h := StaggerPad.run_low s (UInt256.ofNat 4763) ret tailRest (by omega) hrun hactive hfit
    rw [low_end] at h
    exact h

def gasSteps_branch_taken (s : State) (c : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) (hc : UInt256.isTrue c)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4804, stack := c :: rho}
      {s with pc := UInt256.ofNat 904, stack := rho} := by
  apply PadLift.gasSteps_of_raw branchSite {s with pc := UInt256.ofNat 4804, stack := c :: rho} _ hcode hfork hrun hnp branch_pc.symm branch_advances
  exact StaggerPad.run_branch_taken s (UInt256.ofNat 4804) c rho hstack hrun hc (valid_rounds s hcode)

def gasSteps_branch_fall (s : State) (c : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) (hc : ¬ UInt256.isTrue c)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4804, stack := c :: rho}
      {s with pc := UInt256.ofNat 4808, stack := rho} := by
  apply PadLift.gasSteps_of_raw branchSite {s with pc := UInt256.ofNat 4804, stack := c :: rho} _ hcode hfork hrun hnp branch_pc.symm branch_advances
  have h := StaggerPad.run_branch_fall s (UInt256.ofNat 4804) c rho hstack hrun hc
  rw [branch_end] at h
  exact h

def gasSteps_high (s : State) (ret : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 896) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4808, stack := ret :: rest}
      {s with
        pc := UInt256.ofNat 4836
        stack := ret :: rest
        memory := StaggerTablePad.highStores s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  apply PadLift.gasSteps_of_raw highSite {s with pc := UInt256.ofNat 4808, stack := ret :: rest} _ hcode hfork hrun hnp high_pc.symm high_advances
  have h := StaggerPad.run_high s (UInt256.ofNat 4808) ret rest (by omega) hrun hactive hfit
  rw [high_end] at h
  exact h
#print axioms gasSteps_normal
#print axioms gasSteps_low
#print axioms gasSteps_branch_taken
#print axioms gasSteps_branch_fall
#print axioms gasSteps_high
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerSetupSites
