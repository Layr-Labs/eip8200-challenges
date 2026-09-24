import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open J2Raw J2Moves StackRoundTrace StackRoundTemplate
structure Env (s : State) : Prop where
  code : s.executionEnv.code = Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

private theorem code_bound : Artifact.submissionArtifact.code.size < 2^256 := by
  change submissionBytecode.size < 2^256
  rw [referenceBytecode_size]
  decide

namespace initSite
abbrev template : List Instr := J2Raw.initTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 148).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 148 actual_slice
    (by change 148 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 250 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 148) = UInt256.ofNat 250
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 250) template = UInt256.ofNat 315 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 250 stack) = some t) : GasSteps (atState s 250 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end initSite

namespace firstSite
abbrev template : List Instr := J2Raw.firstTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 175).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 175 actual_slice
    (by change 175 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 315 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 175) = UInt256.ofNat 315
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 315) template = UInt256.ofNat 323 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 315 stack) = some t) : GasSteps (atState s 315 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end firstSite

namespace normalSite
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 180).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 180 actual_slice
    (by change 180 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 323 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 180) = UInt256.ofNat 323
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 323) template = UInt256.ofNat 343 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 323 stack) = some t) : GasSteps (atState s 323 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normalSite

namespace normalGuardSite
abbrev template : List Instr := J2Raw.normalGuardTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 199).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 199 actual_slice
    (by change 199 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 343 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 199) = UInt256.ofNat 343
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 343) template = UInt256.ofNat 350 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 343 stack) = some t) : GasSteps (atState s 343 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normalGuardSite

namespace tailSite
abbrev template : List Instr := J2Raw.tailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 204).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 204 actual_slice
    (by change 204 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 350 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 204) = UInt256.ofNat 350
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 350) template = UInt256.ofNat 363 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 350 stack) = some t) : GasSteps (atState s 350 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end tailSite

namespace finishSite
abbrev template : List Instr := J2Raw.finishTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 216).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 216 actual_slice
    (by change 216 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 363 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 216) = UInt256.ofNat 363
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 363) template = UInt256.ofNat 370 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 363 stack) = some t) : GasSteps (atState s 363 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finishSite

namespace transitionSite
abbrev template : List Instr := J2Raw.transitionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 221).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 221 actual_slice
    (by change 221 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 370 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 221) = UInt256.ofNat 370
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 370) template = UInt256.ofNat 406 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 370 stack) = some t) : GasSteps (atState s 370 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end transitionSite

namespace transitionGuardSite
abbrev template : List Instr := J2Raw.transitionGuardTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 254).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 254 actual_slice
    (by change 254 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 406 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 254) = UInt256.ofNat 406
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 406) template = UInt256.ofNat 413 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 406 stack) = some t) : GasSteps (atState s 406 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end transitionGuardSite

namespace toTailSite
abbrev template : List Instr := J2Raw.toTailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 259).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 259 actual_slice
    (by change 259 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 413 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 259) = UInt256.ofNat 413
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 413) template = UInt256.ofNat 417 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 413 stack) = some t) : GasSteps (atState s 413 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end toTailSite

namespace resultSite
abbrev template : List Instr := J2Raw.resultTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 308).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 308 actual_slice
    (by change 308 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 540 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 308) = UInt256.ofNat 540
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 540) template = UInt256.ofNat 545 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 540 stack) = some t) : GasSteps (atState s 540 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end resultSite

namespace genericEntrySite
def template : List Instr := [.op .JUMPDEST]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 326).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 326 actual_slice
    (by change 326 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 568 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 326) = UInt256.ofNat 568
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 568 stack) = some t) : GasSteps (atState s 568 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end genericEntrySite

def gasSteps_generic_entry (s : State) (e : Env s) (stack : List UInt256)
    (hstack : stack.length < 1024) : GasSteps (atState s 568 stack) (atState s 569 stack) := by
  apply genericEntrySite.lift s _ e stack
  simpa only [genericEntrySite.template, atState,
    show UInt256.ofNat 568 + UInt256.ofNat 1 = UInt256.ofNat 569 by decide]
    using PadJump.run_merge s (UInt256.ofNat 568) stack hstack e.run


theorem valid_190 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 323 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 180 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 180 = 323 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_219 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 350 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 204 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 204 = 350 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_298 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 540 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 308 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 308 = 540 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_341 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 568 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 326 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 326 = 568 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

def moves (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length≤990) : Moves s rho where
  init := by
    apply initSite.lift s _ e rho
    simpa only [atState, initSite.end_pc] using run_init s (UInt256.ofNat 250) rho hs e.run
  normal f := by
    apply normalSite.lift s _ e (frame f rho)
    simpa only [atState, normalSite.end_pc] using run_normal s (UInt256.ofNat 323) f rho hs e.run
  tail f := by
    apply tailSite.lift s _ e (frame f rho)
    simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 350) f rho hs e.run
  transition f hlen := by
    apply transitionSite.lift s _ e (frame f rho)
    simpa only [atState, transitionSite.end_pc] using run_transition s (UInt256.ofNat 370) f rho hs e.run hlen
  first f := by
    apply firstSite.lift s _ e (frame f rho)
    have h := run_first s (UInt256.ofNat 315) f rho hs e.run (valid_219 s e)
    by_cases hc : 219 < f.full.toNat
    · simpa only [atState, firstSite.end_pc, if_pos hc] using h
    · simpa only [atState, firstSite.end_pc, if_neg hc] using h
  normalGuard f := by
    apply normalGuardSite.lift s _ e (frame f rho)
    have h := run_normalGuard s (UInt256.ofNat 343) f rho hs e.run (valid_190 s e)
    by_cases hc : f.off.toNat<f.full.toNat
    · simpa only [atState, normalGuardSite.end_pc, if_pos hc] using h
    · simpa only [atState, normalGuardSite.end_pc, if_neg hc] using h
  finish f hlen := by
    apply finishSite.lift s _ e (frame f rho)
    have h := run_finish s (UInt256.ofNat 363) f rho hs e.run hlen (valid_298 s e)
    by_cases hc : f.stop.toNat=f.len.toNat
    · simpa only [atState, finishSite.end_pc, if_pos hc] using h
    · simpa only [atState, finishSite.end_pc, if_neg hc] using h
  transitionGuard f := by
    apply transitionGuardSite.lift s _ e (frame f rho)
    have h := run_transitionGuard s (UInt256.ofNat 406) f rho hs e.run (valid_190 s e)
    by_cases hc : f.off.toNat<f.full.toNat
    · simpa only [atState, transitionGuardSite.end_pc, if_pos hc] using h
    · simpa only [atState, transitionGuardSite.end_pc, if_neg hc] using h
  result f := by
    apply resultSite.lift s _ e (frame f rho)
    have h := run_result s (UInt256.ofNat 540) f rho hs e.run (valid_341 s e)
    by_cases hc : f.acc.toNat=0
    · simpa only [atState, resultSite.end_pc, if_pos hc] using h
    · simpa only [atState, resultSite.end_pc, if_neg hc] using h
  toTail f := by
    apply toTailSite.lift s _ e (frame f rho)
    have hc : (frame f rho).length≤1022 := by simp only [frame, List.length_append, List.length_cons, List.length_nil]; omega
    simpa only [atState] using run_toTail s (UInt256.ofNat 413) (frame f rho) hc e.run (valid_219 s e)

#print axioms moves
#print axioms gasSteps_generic_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
