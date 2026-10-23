import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Run
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StackRoundData
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Sites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
structure Env (s : State) : Prop where
  code : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

namespace special
abbrev template : List Instr := [.op .JUMPDEST]
theorem actual_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 73).take template.length = template := by rfl
def site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 73 actual_slice
    (by change 73 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 143 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 73) = UInt256.ofNat 143
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 143) template = UInt256.ofNat 144 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 143 stack) = some t) :
    GasSteps (atState s 143 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 143 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end special

namespace lower
abbrev template : List Instr := [.op .JUMPDEST]
theorem actual_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 177).take template.length = template := by rfl
def site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 177 actual_slice
    (by change 177 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 497 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 177) = UInt256.ofNat 497
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 497) template = UInt256.ofNat 498 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 497 stack) = some t) :
    GasSteps (atState s 497 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 497 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end lower

namespace combined
abbrev template : List Instr := HoistedInherited.Shared32SparseRun.combinedTemplate
theorem actual_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 78).take template.length = template := by rfl
def site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 78 actual_slice
    (by change 78 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 151 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 78) = UInt256.ofNat 151
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 151) template = UInt256.ofNat 188 := by decide

def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 151 stack) = some t) :
    GasSteps (atState s 151 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 151 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end combined


namespace table
abbrev template : List Instr := HoistedInherited.Shared32Run.template
theorem actual_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 178).take template.length = template := by rfl
def site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 178 actual_slice
    (by change 178 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 498 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 178) = UInt256.ofNat 498
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 498) template = UInt256.ofNat 824 := by decide

/-- `MCOPY` advances the pc like any straight-line instruction, but it is outside
`PadLift.advancesCheck`'s whitelist and the S51 schedule fan uses two of them. -/
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
      | exact mcopy_pc hresult
      | exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ h) hresult
      | (rename_i inner; cases inner <;> first
          | exact mcopy_pc hresult
          | exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ h) hresult)

private theorem advances (instruction : Instr) (hi : instruction ∈ template.dropLast)
    {s t : State} (hr : DataStepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  have hall : template.dropLast.all advancesCheck = true := by decide
  exact advancesCheck_sound instruction ((List.all_eq_true.mp hall) instruction hi) hr

def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 498 stack) = some t) :
    GasSteps (atState s 498 stack) t := by
  let u := atState s 498 stack
  apply DataStepper.runLocatedBlock_sound HoistedInherited.Artifact.submissionArtifact .Osaka site.path (s := u) (t := t) e.code e.fork
  · have hl := runLocatedBlock_eq_raw_terminal_sites site.sites template
      site.instruction_eq site.contiguous u
      (by rw [site.head_eq]; exact congrArg some site_pc) (by
        intro located hmem a b hr
        apply advances _ ?_ hr
        have hm : located.located.instruction ∈
            site.sites.dropLast.map (fun item => item.located.instruction) := List.mem_map_of_mem hmem
        rw [List.map_dropLast, site.instruction_eq] at hm
        exact hm)
    change DataStepper.runLocatedBlock (LocatedSite.path site.sites) u = some t
    rw [hl]
    exact h
  · exact e.run
  · exact e.np
end table


namespace missJump
abbrev template : List Instr := HoistedInherited.Shared32SparseRun.missJumpTemplate
theorem actual_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 83).take template.length = template := by rfl
def site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 83 actual_slice
    (by change 83 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 188 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 83) = UInt256.ofNat 188
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 188) template = UInt256.ofNat 192 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 188 stack) = some t) :
    GasSteps (atState s 188 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 188 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end missJump

namespace missTail
abbrev template : List Instr := [ .op .JUMPDEST ]
theorem actual_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 5392).take template.length = template := by rfl
def site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 5392 actual_slice
    (by change 5392 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 9715 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 5392) = UInt256.ofNat 9715
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 9715 stack) = some t) :
    GasSteps (atState s 9715 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 9715 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end missTail

theorem valid_special (s : State) (e : Env s) :
    Decode.isValidJumpDest s.executionEnv.code 143 = true := by
  have hpc : HoistedInherited.Artifact.submissionArtifact.instructionPC 73 = 143 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := HoistedInherited.Artifact.submissionArtifact.isValidJumpDest_index 73 (by rfl)
  rw [hpc] at h
  rw [e.code]
  exact h

theorem valid_lower (s : State) (e : Env s) :
    Decode.isValidJumpDest s.executionEnv.code 497 = true := by
  have hpc : HoistedInherited.Artifact.submissionArtifact.instructionPC 177 = 497 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := HoistedInherited.Artifact.submissionArtifact.isValidJumpDest_index 177 (by rfl)
  rw [hpc] at h
  rw [e.code]
  exact h

namespace head
abbrev template : List Instr := HoistedInherited.Shared32SparseRun.headTemplate
theorem actual_slice : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 74).take template.length = template := by rfl
def site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 74 actual_slice
    (by change 74 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 144 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 74) = UInt256.ofNat 144
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 144) template = UInt256.ofNat 151 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 144 stack) = some t) :
    GasSteps (atState s 144 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 144 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end head


#print axioms table.lift
#print axioms combined.lift
#print axioms head.lift
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Sites
