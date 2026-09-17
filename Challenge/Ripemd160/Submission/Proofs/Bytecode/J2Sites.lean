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
theorem site_pc : site.startPC = UInt256.ofNat 110 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 68) = UInt256.ofNat 110
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 110) template = UInt256.ofNat 177 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 110 stack) = some t) : GasSteps (atState s 110 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end initSite

namespace firstSite
abbrev template : List Instr := J2Raw.firstTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 96).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 96 actual_slice
    (by change 96 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 177 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 96) = UInt256.ofNat 177
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 177) template = UInt256.ofNat 182 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 177 stack) = some t) : GasSteps (atState s 177 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end firstSite

namespace normalSite
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 100).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 100 actual_slice
    (by change 100 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 182 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 100) = UInt256.ofNat 182
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 182) template = UInt256.ofNat 205 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 182 stack) = some t) : GasSteps (atState s 182 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normalSite

namespace normalGuardSite
abbrev template : List Instr := J2Raw.normalGuardTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 122).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 122 actual_slice
    (by change 122 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 205 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 122) = UInt256.ofNat 205
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 205) template = UInt256.ofNat 211 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 205 stack) = some t) : GasSteps (atState s 205 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normalGuardSite

namespace tailSite
abbrev template : List Instr := J2Raw.tailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 127).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 127 actual_slice
    (by change 127 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 211 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 127) = UInt256.ofNat 211
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 211) template = UInt256.ofNat 229 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 211 stack) = some t) : GasSteps (atState s 211 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end tailSite

namespace finishSite
abbrev template : List Instr := J2Raw.finishTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 142).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 142 actual_slice
    (by change 142 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 229 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 142) = UInt256.ofNat 229
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 229) template = UInt256.ofNat 236 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 229 stack) = some t) : GasSteps (atState s 229 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finishSite

namespace transitionSite
abbrev template : List Instr := J2Raw.transitionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 147).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 147 actual_slice
    (by change 147 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 236 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 147) = UInt256.ofNat 236
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 236) template = UInt256.ofNat 279 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 236 stack) = some t) : GasSteps (atState s 236 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end transitionSite

namespace transitionGuardSite
abbrev template : List Instr := J2Raw.transitionGuardTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 186).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 186 actual_slice
    (by change 186 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 279 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 186) = UInt256.ofNat 279
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 279) template = UInt256.ofNat 285 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 279 stack) = some t) : GasSteps (atState s 279 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end transitionGuardSite

namespace toTailSite
abbrev template : List Instr := J2Raw.toTailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 191).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 191 actual_slice
    (by change 191 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 285 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 191) = UInt256.ofNat 285
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 285) template = UInt256.ofNat 288 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 285 stack) = some t) : GasSteps (atState s 285 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end toTailSite

namespace resultSite
abbrev template : List Instr := J2Raw.resultTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 193).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 193 actual_slice
    (by change 193 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 288 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 193) = UInt256.ofNat 288
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 288) template = UInt256.ofNat 293 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 288 stack) = some t) : GasSteps (atState s 288 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end resultSite



theorem valid_190 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 182 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 100 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 100 = 182 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_219 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 211 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 127 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 127 = 211 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_298 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 288 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 193 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 193 = 288 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_341 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 330 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 220 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 220 = 330 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

def moves (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length≤990) : Moves s rho where
  init := by
    apply initSite.lift s _ e rho
    simpa only [atState, initSite.end_pc] using run_init s (UInt256.ofNat 110) rho hs e.run
  normal f := by
    apply normalSite.lift s _ e (frame f rho)
    simpa only [atState, normalSite.end_pc] using run_normal s (UInt256.ofNat 182) f rho hs e.run
  tail f := by
    apply tailSite.lift s _ e (frame f rho)
    simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 211) f rho hs e.run
  transition f hlen := by
    apply transitionSite.lift s _ e (frame f rho)
    simpa only [atState, transitionSite.end_pc] using run_transition s (UInt256.ofNat 236) f rho hs e.run hlen
  first f := by
    apply firstSite.lift s _ e (frame f rho)
    have h := run_first s (UInt256.ofNat 177) f rho hs e.run (valid_219 s e)
    by_cases hc : f.full.toNat=0
    · simpa only [atState, firstSite.end_pc, if_pos hc] using h
    · simpa only [atState, firstSite.end_pc, if_neg hc] using h
  normalGuard f := by
    apply normalGuardSite.lift s _ e (frame f rho)
    have h := run_normalGuard s (UInt256.ofNat 205) f rho hs e.run (valid_190 s e)
    by_cases hc : f.off.toNat<f.full.toNat
    · simpa only [atState, normalGuardSite.end_pc, if_pos hc] using h
    · simpa only [atState, normalGuardSite.end_pc, if_neg hc] using h
  finish f hlen := by
    apply finishSite.lift s _ e (frame f rho)
    have h := run_finish s (UInt256.ofNat 229) f rho hs e.run hlen (valid_298 s e)
    by_cases hc : f.stop.toNat=f.len.toNat
    · simpa only [atState, finishSite.end_pc, if_pos hc] using h
    · simpa only [atState, finishSite.end_pc, if_neg hc] using h
  transitionGuard f := by
    apply transitionGuardSite.lift s _ e (frame f rho)
    have h := run_transitionGuard s (UInt256.ofNat 279) f rho hs e.run (valid_190 s e)
    by_cases hc : f.off.toNat<f.full.toNat
    · simpa only [atState, transitionGuardSite.end_pc, if_pos hc] using h
    · simpa only [atState, transitionGuardSite.end_pc, if_neg hc] using h
  result f := by
    apply resultSite.lift s _ e (frame f rho)
    have h := run_result s (UInt256.ofNat 288) f rho hs e.run (valid_341 s e)
    by_cases hc : f.acc.toNat=0
    · simpa only [atState, resultSite.end_pc, if_pos hc] using h
    · simpa only [atState, resultSite.end_pc, if_neg hc] using h
  toTail f := by
    apply toTailSite.lift s _ e (frame f rho)
    have hc : (frame f rho).length≤1022 := by simp only [frame, List.length_append, List.length_cons, List.length_nil]; omega
    simpa only [atState] using run_toTail s (UInt256.ofNat 285) (frame f rho) hc e.run (valid_219 s e)

#print axioms moves
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
