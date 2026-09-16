import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 68).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 68 actual_slice
    (by change 68 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 112 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 68) = UInt256.ofNat 112
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 112) template = UInt256.ofNat 183 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 112 stack) = some t) : GasSteps (atState s 112 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end initSite

namespace firstSite
abbrev template : List Instr := J2Raw.firstTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 99).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 99 actual_slice
    (by change 99 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 183 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 99) = UInt256.ofNat 183
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 183) template = UInt256.ofNat 188 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 183 stack) = some t) : GasSteps (atState s 183 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end firstSite

namespace normalSite
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 103).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 103 actual_slice
    (by change 103 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 188 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 103) = UInt256.ofNat 188
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 188) template = UInt256.ofNat 211 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 188 stack) = some t) : GasSteps (atState s 188 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normalSite

namespace normalGuardSite
abbrev template : List Instr := J2Raw.normalGuardTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 125).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 125 actual_slice
    (by change 125 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 211 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 125) = UInt256.ofNat 211
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 211) template = UInt256.ofNat 217 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 211 stack) = some t) : GasSteps (atState s 211 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normalGuardSite

namespace tailSite
abbrev template : List Instr := J2Raw.tailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 130).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 130 actual_slice
    (by change 130 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 217 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 130) = UInt256.ofNat 217
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 217) template = UInt256.ofNat 235 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 217 stack) = some t) : GasSteps (atState s 217 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end tailSite

namespace finishSite
abbrev template : List Instr := J2Raw.finishTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 145).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 145 actual_slice
    (by change 145 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 235 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 145) = UInt256.ofNat 235
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 235) template = UInt256.ofNat 242 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 235 stack) = some t) : GasSteps (atState s 235 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finishSite

namespace transitionSite
abbrev template : List Instr := J2Raw.transitionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 150).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 150 actual_slice
    (by change 150 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 242 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 150) = UInt256.ofNat 242
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 242) template = UInt256.ofNat 283 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 242 stack) = some t) : GasSteps (atState s 242 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end transitionSite

namespace transitionGuardSite
abbrev template : List Instr := J2Raw.transitionGuardTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 187).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 187 actual_slice
    (by change 187 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 283 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 187) = UInt256.ofNat 283
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 283) template = UInt256.ofNat 289 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 283 stack) = some t) : GasSteps (atState s 283 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end transitionGuardSite

namespace toTailSite
abbrev template : List Instr := J2Raw.toTailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 192).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 192 actual_slice
    (by change 192 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 289 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 192) = UInt256.ofNat 289
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 289) template = UInt256.ofNat 292 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 289 stack) = some t) : GasSteps (atState s 289 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end toTailSite

namespace resultSite
abbrev template : List Instr := J2Raw.resultTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 194).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 194 actual_slice
    (by change 194 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 292 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 194) = UInt256.ofNat 292
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 292) template = UInt256.ofNat 297 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 292 stack) = some t) : GasSteps (atState s 292 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end resultSite



theorem valid_190 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 188 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 103 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 103 = 188 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_219 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 217 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 130 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 130 = 217 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_298 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 292 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 194 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 194 = 292 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_341 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 336 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 221 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 221 = 336 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

def moves (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length≤990) : Moves s rho where
  init := by
    apply initSite.lift s _ e rho
    simpa only [atState, initSite.end_pc] using run_init s (UInt256.ofNat 112) rho hs e.run
  normal f := by
    apply normalSite.lift s _ e (frame f rho)
    simpa only [atState, normalSite.end_pc] using run_normal s (UInt256.ofNat 188) f rho hs e.run
  tail f := by
    apply tailSite.lift s _ e (frame f rho)
    simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 217) f rho hs e.run
  transition f hlen := by
    apply transitionSite.lift s _ e (frame f rho)
    simpa only [atState, transitionSite.end_pc] using run_transition s (UInt256.ofNat 242) f rho hs e.run hlen
  first f := by
    apply firstSite.lift s _ e (frame f rho)
    have h := run_first s (UInt256.ofNat 183) f rho hs e.run (valid_219 s e)
    by_cases hc : f.full.toNat=0
    · simpa only [atState, firstSite.end_pc, if_pos hc] using h
    · simpa only [atState, firstSite.end_pc, if_neg hc] using h
  normalGuard f := by
    apply normalGuardSite.lift s _ e (frame f rho)
    have h := run_normalGuard s (UInt256.ofNat 211) f rho hs e.run (valid_190 s e)
    by_cases hc : f.off.toNat<f.full.toNat
    · simpa only [atState, normalGuardSite.end_pc, if_pos hc] using h
    · simpa only [atState, normalGuardSite.end_pc, if_neg hc] using h
  finish f hlen := by
    apply finishSite.lift s _ e (frame f rho)
    have h := run_finish s (UInt256.ofNat 235) f rho hs e.run hlen (valid_298 s e)
    by_cases hc : f.stop.toNat=f.len.toNat
    · simpa only [atState, finishSite.end_pc, if_pos hc] using h
    · simpa only [atState, finishSite.end_pc, if_neg hc] using h
  transitionGuard f := by
    apply transitionGuardSite.lift s _ e (frame f rho)
    have h := run_transitionGuard s (UInt256.ofNat 283) f rho hs e.run (valid_190 s e)
    by_cases hc : f.off.toNat<f.full.toNat
    · simpa only [atState, transitionGuardSite.end_pc, if_pos hc] using h
    · simpa only [atState, transitionGuardSite.end_pc, if_neg hc] using h
  result f := by
    apply resultSite.lift s _ e (frame f rho)
    have h := run_result s (UInt256.ofNat 292) f rho hs e.run (valid_341 s e)
    by_cases hc : f.acc.toNat=0
    · simpa only [atState, resultSite.end_pc, if_pos hc] using h
    · simpa only [atState, resultSite.end_pc, if_neg hc] using h
  toTail f := by
    apply toTailSite.lift s _ e (frame f rho)
    have hc : (frame f rho).length≤1022 := by simp only [frame, List.length_append, List.length_cons, List.length_nil]; omega
    simpa only [atState] using run_toTail s (UInt256.ofNat 289) (frame f rho) hc e.run (valid_219 s e)

#print axioms moves
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
