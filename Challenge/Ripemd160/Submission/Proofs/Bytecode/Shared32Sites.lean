import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Run
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
structure Env (s : State) : Prop where
  code : s.executionEnv.code = Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

namespace special
abbrev template : List Instr := [.op .JUMPDEST]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 79).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 79 actual_slice
    (by change 79 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 143 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 79) = UInt256.ofNat 143
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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 209).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 209 actual_slice
    (by change 209 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 494 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 209) = UInt256.ofNat 494
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 494) template = UInt256.ofNat 495 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 494 stack) = some t) :
    GasSteps (atState s 494 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 494 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end lower

namespace sparse
abbrev template : List Instr := Shared32SparseRun.template
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 84).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 84 actual_slice
    (by change 84 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 151 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 84) = UInt256.ofNat 151
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 151) template = UInt256.ofNat 158 := by decide
private theorem mstore8_pc {s t : State}
    (hresult : DataStepper.runInstr (.op .MSTORE8) s = some t) :
    t.pc = s.pc + UInt256.ofNat 1 := by
  by_cases hcap : s.stack.length < 1024
  · simp only [DataStepper.runInstr, if_pos hcap] at hresult
    cases hs : s.stack with
    | nil => simp [hs] at hresult
    | cons a tail =>
      cases ht : tail with
      | nil => simp [hs, ht] at hresult
      | cons b rest =>
        simp [hs, ht] at hresult
        subst t
        rfl
  · simp [DataStepper.runInstr, hcap] at hresult

private theorem advances (instruction : Instr) (hi : instruction ∈ template.dropLast)
    {s t : State} (hr : DataStepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  simp only [template, Shared32SparseRun.template, List.dropLast_cons_cons,
    List.dropLast_singleton, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h
  all_goals subst instruction
  all_goals first
    | exact mstore8_pc hr
    | exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ (by decide)) hr

def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 151 stack) = some t) :
    GasSteps (atState s 151 stack) t := by
  let u := atState s 151 stack
  apply DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka site.path (s := u) (t := t) e.code e.fork
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
end sparse


namespace table
abbrev template : List Instr := Shared32Run.template
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 210).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 210 actual_slice
    (by change 210 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 495 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 210) = UInt256.ofNat 495
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 495) template = UInt256.ofNat 824 := by decide

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
    (h : runInstrSeq template (atState s 495 stack) = some t) :
    GasSteps (atState s 495 stack) t := by
  let u := atState s 495 stack
  apply DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka site.path (s := u) (t := t) e.code e.fork
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

namespace guard
abbrev template : List Instr := [ .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .EQ,
    .push ⟨2, by decide⟩ (UInt256.ofNat 494),
    .op .JUMPI ]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 89).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 89 actual_slice
    (by change 89 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 158 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 89) = UInt256.ofNat 158
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 158) template = UInt256.ofNat 166 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 158 stack) = some t) :
    GasSteps (atState s 158 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 158 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end guard

theorem valid_special (s : State) (e : Env s) :
    Decode.isValidJumpDest s.executionEnv.code 143 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 79 = 143 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 79 (by rfl)
  rw [hpc] at h
  rw [e.code]
  exact h

theorem valid_lower (s : State) (e : Env s) :
    Decode.isValidJumpDest s.executionEnv.code 494 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 209 = 494 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 209 (by rfl)
  rw [hpc] at h
  rw [e.code]
  exact h

namespace head
abbrev template : List Instr := Shared32SparseRun.headTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 80).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 80 actual_slice
    (by change 80 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 144 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 80) = UInt256.ofNat 144
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 144) template = UInt256.ofNat 149 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 144 stack) = some t) :
    GasSteps (atState s 144 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 144 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end head

namespace fold
abbrev template : List Instr := Shared32SparseRun.foldTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 83).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 83 actual_slice
    (by change 83 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 149 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 83) = UInt256.ofNat 149
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 149) template = UInt256.ofNat 151 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 149 stack) = some t) :
    GasSteps (atState s 149 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 149 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end fold

#print axioms table.lift
#print axioms sparse.lift
#print axioms guard.lift
#print axioms head.lift
#print axioms fold.lift
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
