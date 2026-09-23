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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 70).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 70 actual_slice
    (by change 70 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 118 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 70) = UInt256.ofNat 118
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 118) template = UInt256.ofNat 119 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 118 stack) = some t) :
    GasSteps (atState s 118 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 118 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end special

namespace lower
abbrev template : List Instr := [.op .JUMPDEST]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 378).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 378 actual_slice
    (by change 378 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 812 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 378) = UInt256.ofNat 812
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 812) template = UInt256.ofNat 813 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 812 stack) = some t) :
    GasSteps (atState s 812 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 812 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end lower

namespace sparse
abbrev template : List Instr := Shared32SparseRun.template
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 72).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 72 actual_slice
    (by change 72 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 121 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 72) = UInt256.ofNat 121
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 121) template = UInt256.ofNat 128 := by decide
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
    (h : runInstrSeq template (atState s 121 stack) = some t) :
    GasSteps (atState s 121 stack) t := by
  let u := atState s 121 stack
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

namespace jump
abbrev template : List Instr := PadJump.template 812
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 77).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 77 actual_slice
    (by change 77 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 128 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 77) = UInt256.ofNat 128
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 128) template = UInt256.ofNat 132 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 128 stack) = some t) :
    GasSteps (atState s 128 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 128 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end jump

namespace table
abbrev template : List Instr := Shared32Run.template
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 379).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 379 actual_slice
    (by change 379 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 813 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 379) = UInt256.ofNat 813
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 813) template = UInt256.ofNat 1130 := by decide

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
    (h : runInstrSeq template (atState s 813 stack) = some t) :
    GasSteps (atState s 813 stack) t := by
  let u := atState s 813 stack
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
    .push ⟨1, by decide⟩ (UInt256.ofNat 118),
    .op .JUMPI ]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 107).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 107 actual_slice
    (by change 107 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 194 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 107) = UInt256.ofNat 194
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 194) template = UInt256.ofNat 201 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 194 stack) = some t) :
    GasSteps (atState s 194 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 194 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end guard

theorem valid_special (s : State) (e : Env s) :
    Decode.isValidJumpDest s.executionEnv.code 118 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 70 = 118 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 70 (by rfl)
  rw [hpc] at h
  rw [e.code]
  exact h

theorem valid_lower (s : State) (e : Env s) :
    Decode.isValidJumpDest s.executionEnv.code 812 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 378 = 812 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 378 (by rfl)
  rw [hpc] at h
  rw [e.code]
  exact h

namespace marker
abbrev template : List Instr := [.push ⟨1, by decide⟩ (UInt256.ofNat 128)]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 71).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 71 actual_slice
    (by change 71 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 119 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 71) = UInt256.ofNat 119
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 119) template = UInt256.ofNat 121 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 119 stack) = some t) :
    GasSteps (atState s 119 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 119 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end marker

#print axioms table.lift
#print axioms sparse.lift
#print axioms guard.lift
#print axioms marker.lift
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
