import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80NoJumpdest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentMaskEndian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPadSetup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinarySites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace Table80Setup

def actualNormalTemplate : List Instr := PersistentMaskEndian.normalTemplate

theorem normal_slice :
    (Artifact.submissionArtifact.instructions.drop 175).take actualNormalTemplate.length = actualNormalTemplate := by rfl

def normalSite : GenericRoundSite Artifact.submissionArtifact .Osaka actualNormalTemplate :=
  StackSiteBuilder.ofSlice actualNormalTemplate 175 normal_slice
    (by change 175 + actualNormalTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := actualNormalTemplate) (by decide))
    (by decide)
theorem normal_pc : normalSite.startPC = UInt256.ofNat 458 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 175) = UInt256.ofNat 458
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- `MCOPY` is a straight-line instruction, but it is outside `PadLift.advancesCheck`'s
whitelist, and the S51 schedule fan uses two of them. -/
private theorem mcopy_pc {s t : State}
    (hresult : DataStepper.runInstr (.op .MCOPY) s = some t) :
    t.pc = s.pc + UInt256.ofNat 1 := by
  by_cases hcap : s.stack.length < 1024
  · simp only [DataStepper.runInstr, if_pos hcap] at hresult
    cases hs : s.stack with
    | nil => simp [hs] at hresult
    | cons a tail =>
      cases ht : tail with
      | nil => simp [hs, ht] at hresult
      | cons b rest =>
        cases hu : rest with
        | nil => simp [hs, ht, hu] at hresult
        | cons c rest2 =>
          simp [hs, ht, hu] at hresult
          subst t
          rfl
  · simp [DataStepper.runInstr, hcap] at hresult

private def advancesCheck : Instr → Bool
  | .op .DIV => true
  | .op .MCOPY => true
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
      | exact mcopy_pc hresult
      | exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ h) hresult
      | (rename_i inner; cases inner <;> first
          | exact PairedDivMaskCache.runInstr_pc_div hresult
          | exact mcopy_pc hresult
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

theorem normal_end : pcAfter (UInt256.ofNat 458) actualNormalTemplate = UInt256.ofNat 808 := by decide

theorem low_slice :
    (Artifact.submissionArtifact.instructions.drop 80).take StaggerPad.lowTemplate.length = StaggerPad.lowTemplate := by rfl

def lowSite : GenericRoundSite Artifact.submissionArtifact .Osaka StaggerPad.lowTemplate :=
  StackSiteBuilder.ofSlice StaggerPad.lowTemplate 80 low_slice
    (by change 80 + StaggerPad.lowTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := StaggerPad.lowTemplate) (by decide))
    (by decide)
theorem low_pc : lowSite.startPC = UInt256.ofNat 130 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 80) = UInt256.ofNat 130
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem low_advances : ∀ instruction ∈ StaggerPad.lowTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem low_end : pcAfter (UInt256.ofNat 130) StaggerPad.lowTemplate = UInt256.ofNat 184 := by decide

open StaggerPad (branchTemplate)

theorem branch_slice :
    (Artifact.submissionArtifact.instructions.drop 102).take branchTemplate.length = branchTemplate := by rfl

def branchSite : GenericRoundSite Artifact.submissionArtifact .Osaka branchTemplate :=
  StackSiteBuilder.ofSlice branchTemplate 102 branch_slice
    (by change 102 + branchTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := branchTemplate) (by decide))
    (by decide)
theorem branch_pc : branchSite.startPC = UInt256.ofNat 184 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 102) = UInt256.ofNat 184
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem branch_advances : ∀ instruction ∈ branchTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem valid_rounds (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 808).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 396 = 808 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 396 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 808 = true
  rw [hcode]
  exact h

def gasSteps_normal (s : State) (ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat)
    (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hp : 1056 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 32 = UInt256.ofNat (p + 32))
    (hq0 : off = UInt256.ofNat p)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 458, stack := PersistentMaskEndian.stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho}
      {s with pc := UInt256.ofNat 808, stack := PersistentMaskEndian.stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho, memory := PoolReference.dataMemory s.memory p, activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p)} := by
  apply normal_gasSteps_of_raw {s with pc := UInt256.ofNat 458, stack := PersistentMaskEndian.stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} _ hcode hfork hrun hnp normal_pc.symm
  have h := PersistentMaskEndian.run_normal s (UInt256.ofNat 458) ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p hstack hrun hp hbound hq1 hq0 rfl
  have hend : pcAfter (UInt256.ofNat 458) PersistentMaskEndian.normalTemplate = UInt256.ofNat 808 := by decide
  rw [hend] at h
  exact h

def gasSteps_low (s : State) (off : UInt256) (rest : List UInt256)
    (hmask : rest.head? = some (UInt256.ofNat 4294967295))
    (hstack : rest.length ≤ 896) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hoff : s.executionEnv.calldata.size ≤ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 130, stack := off :: rest}
      {s with
        pc := UInt256.ofNat 184
        stack := UInt256.ofNat (128 * (1 + 2 ^ 144)) :: rest
        memory := StaggerTablePad.padRealChain s.memory
          (UInt256.ofNat s.executionEnv.calldata.size)} := by
  cases rest with
  | nil => simp at hmask
  | cons mask tailRest =>
    simp only [List.head?_cons, Option.some.injEq] at hmask
    subst mask
    simp only [List.length_cons] at hstack
    apply PadLift.gasSteps_of_raw lowSite {s with pc := UInt256.ofNat 130, stack := off :: UInt256.ofNat 4294967295 :: tailRest} _ hcode hfork hrun hnp low_pc.symm low_advances
    have h := StaggerPad.run_low s (UInt256.ofNat 130) off tailRest (by omega) hrun hactive hfit hoff
    rw [low_end] at h
    exact h

def gasSteps_branch_taken (s : State)
    (a b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 c : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 184, stack := a :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: c :: rho}
      {s with pc := UInt256.ofNat 808, stack := c :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: a :: rho} := by
  apply PadLift.gasSteps_of_raw branchSite {s with pc := UInt256.ofNat 184, stack := a :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: c :: rho} _ hcode hfork hrun hnp branch_pc.symm branch_advances
  exact StaggerPad.run_branch_taken s (UInt256.ofNat 184) a b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 c rho hstack hrun (valid_rounds s hcode)

#print axioms gasSteps_normal
#print axioms gasSteps_low
#print axioms gasSteps_branch_taken
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinarySites
