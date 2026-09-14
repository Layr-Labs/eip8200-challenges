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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 217).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 217 actual_slice
    (by change 217 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 324 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 217) = UInt256.ofNat 324
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 324) template = UInt256.ofNat 325 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 324 stack) = some t) :
    GasSteps (atState s 324 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 324 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end special

namespace lower
abbrev template : List Instr := [.op .JUMPDEST]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 286).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 286 actual_slice
    (by change 286 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 526 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 286) = UInt256.ofNat 526
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 526) template = UInt256.ofNat 527 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 526 stack) = some t) :
    GasSteps (atState s 526 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 526 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end lower

namespace sparse
abbrev template : List Instr := Shared32SparseRun.template
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 219).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 219 actual_slice
    (by change 219 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 326 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 219) = UInt256.ofNat 326
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 326) template = UInt256.ofNat 333 := by decide
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
    (h : runInstrSeq template (atState s 326 stack) = some t) :
    GasSteps (atState s 326 stack) t := by
  let u := atState s 326 stack
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
abbrev template : List Instr := PadJump.template 526
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 224).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 224 actual_slice
    (by change 224 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 333 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 224) = UInt256.ofNat 333
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 333) template = UInt256.ofNat 337 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 333 stack) = some t) :
    GasSteps (atState s 333 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 333 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end jump

namespace table
abbrev template : List Instr := Shared32Run.template
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 287).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 287 actual_slice
    (by change 287 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 527 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 287) = UInt256.ofNat 527
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 527) template = UInt256.ofNat 894 := by decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 527 stack) = some t) :
    GasSteps (atState s 527 stack) t := by
  apply PadLift.gasSteps_of_raw site (atState s 527 stack) t e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact h
end table



theorem valid_special (s : State) (e : Env s) :
    Decode.isValidJumpDest s.executionEnv.code 324 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 217 = 324 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 217 (by rfl)
  rw [hpc] at h
  rw [e.code]
  exact h

theorem valid_lower (s : State) (e : Env s) :
    Decode.isValidJumpDest s.executionEnv.code 526 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 286 = 526 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 286 (by rfl)
  rw [hpc] at h
  rw [e.code]
  exact h

theorem msize_decoded (s : State) (e : Env s) (stack : List UInt256) :
    (atState s 325 stack).decodedOp = some .MSIZE := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 218 .MSIZE
    (by rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of (atState s 325 stack) 218
    e.code ?_ .MSIZE none hd
    (by change Operation.MSIZE.availableInFork s.fork = true; rw [e.fork]; rfl)
  change (UInt256.ofNat 325).toNat = Artifact.submissionArtifact.instructionPC 218
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

#print axioms table.lift
#print axioms sparse.lift
#print axioms msize_decoded
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
