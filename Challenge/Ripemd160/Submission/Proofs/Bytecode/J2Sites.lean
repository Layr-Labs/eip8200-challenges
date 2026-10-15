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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3540).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3540 actual_slice
    (by change 3540 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4808 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3540) = UInt256.ofNat 4808
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4808) template = UInt256.ofNat 4881 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4808 stack) = some t) : GasSteps (atState s 4808 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end initSite

namespace firstSite
abbrev template : List Instr := J2Raw.firstTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3549).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3549 actual_slice
    (by change 3549 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4881 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3549) = UInt256.ofNat 4881
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4881) template = UInt256.ofNat 4889 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4881 stack) = some t) : GasSteps (atState s 4881 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end firstSite

namespace normalSite
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3554).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3554 actual_slice
    (by change 3554 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4889 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3554) = UInt256.ofNat 4889
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4889) template = UInt256.ofNat 4907 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4889 stack) = some t) : GasSteps (atState s 4889 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normalSite

namespace normalGuardSite
abbrev template : List Instr := J2Raw.normalGuardTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3572).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3572 actual_slice
    (by change 3572 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4907 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3572) = UInt256.ofNat 4907
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4907) template = UInt256.ofNat 4914 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4907 stack) = some t) : GasSteps (atState s 4907 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normalGuardSite

namespace tailSite
abbrev template : List Instr := J2Raw.tailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3577).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3577 actual_slice
    (by change 3577 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4914 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3577) = UInt256.ofNat 4914
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4914) template = UInt256.ofNat 4927 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4914 stack) = some t) : GasSteps (atState s 4914 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end tailSite

namespace finishSite
abbrev template : List Instr := J2Raw.finishTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3589).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3589 actual_slice
    (by change 3589 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4927 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3589) = UInt256.ofNat 4927
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4927) template = UInt256.ofNat 4934 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4927 stack) = some t) : GasSteps (atState s 4927 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finishSite

namespace transitionSite
abbrev template : List Instr := J2Raw.transitionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3397).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3397 actual_slice
    (by change 3397 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4547 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3397) = UInt256.ofNat 4547
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4547) template = UInt256.ofNat 4584 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4547 stack) = some t) : GasSteps (atState s 4547 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end transitionSite

namespace transitionGuardSite
abbrev template : List Instr := J2Raw.transitionGuardTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3431).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3431 actual_slice
    (by change 3431 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4584 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3431) = UInt256.ofNat 4584
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4584) template = UInt256.ofNat 4590 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4584 stack) = some t) : GasSteps (atState s 4584 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end transitionGuardSite

namespace toTailSite
abbrev template : List Instr := J2Raw.toTailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3435).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3435 actual_slice
    (by change 3435 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4590 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3435) = UInt256.ofNat 4590
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4590) template = UInt256.ofNat 4594 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4590 stack) = some t) : GasSteps (atState s 4590 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end toTailSite

namespace resultSite
abbrev template : List Instr := J2Raw.resultTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3594).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3594 actual_slice
    (by change 3594 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4934 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3594) = UInt256.ofNat 4934
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4934) template = UInt256.ofNat 4938 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4934 stack) = some t) : GasSteps (atState s 4934 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end resultSite

namespace genericEntrySite
def template : List Instr := [.op .JUMPDEST]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 154).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 154 actual_slice
    (by change 154 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 245 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 154) = UInt256.ofNat 245
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 245 stack) = some t) : GasSteps (atState s 245 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end genericEntrySite

def gasSteps_generic_entry (s : State) (e : Env s) (stack : List UInt256)
    (hstack : stack.length < 1024) : GasSteps (atState s 245 stack) (atState s 246 stack) := by
  apply genericEntrySite.lift s _ e stack
  simpa only [genericEntrySite.template, atState,
    show UInt256.ofNat 245 + UInt256.ofNat 1 = UInt256.ofNat 246 by decide]
    using PadJump.run_merge s (UInt256.ofNat 245) stack hstack e.run


theorem valid_190 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4889 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3554 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3554 = 4889 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_219 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4914 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3577 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3577 = 4914 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_298 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4547 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3397 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3397 = 4547 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_341 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4959 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3614 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3614 = 4959 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

def movesOf (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length≤990)
    (hactive : s.activeWords = UInt256.ofNat 1)
    (hinit : GasSteps (atState s 4808 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
      (atState s 4881 (frame (initResult s.executionEnv.calldata.size) rho))) : Moves s rho where
  init := hinit
  normal f := by
    apply normalSite.lift s _ e (frame f rho)
    simpa only [atState, normalSite.end_pc] using run_normal s (UInt256.ofNat 4889) f rho hs e.run hactive
  tail f := by
    apply tailSite.lift s _ e (frame f rho)
    simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 4914) f rho hs e.run
  transition f hlen := by
    apply transitionSite.lift s _ e (frame f rho)
    simpa only [atState, transitionSite.end_pc] using run_transition s (UInt256.ofNat 4547) f rho hs e.run hlen hactive
  first f hlen := by
    apply firstSite.lift s _ e (frame f rho)
    have h := run_first s (UInt256.ofNat 4881) f rho hs e.run hlen (valid_219 s e)
    by_cases hc : f.len.toNat < 33
    · simpa only [atState, firstSite.end_pc, if_pos hc] using h
    · simpa only [atState, firstSite.end_pc, if_neg hc] using h
  normalGuard f := by
    apply normalGuardSite.lift s _ e (frame f rho)
    have h := run_normalGuard s (UInt256.ofNat 4907) f rho hs e.run (valid_190 s e)
    by_cases hc : f.off.toNat<f.full.toNat
    · simpa only [atState, normalGuardSite.end_pc, if_pos hc] using h
    · simpa only [atState, normalGuardSite.end_pc, if_neg hc] using h
  finish f hlen := by
    apply finishSite.lift s _ e (frame f rho)
    have h := run_finish s (UInt256.ofNat 4927) f rho hs e.run hlen (valid_298 s e)
    by_cases hc : f.stop.toNat=f.len.toNat
    · simpa only [atState, finishSite.end_pc, if_pos hc] using h
    · simpa only [atState, finishSite.end_pc, if_neg hc] using h
  result f := by
    apply resultSite.lift s _ e (frame f rho)
    have h := run_result s (UInt256.ofNat 4934) f rho hs e.run (valid_341 s e)
    by_cases hc : f.acc.toNat=0
    · simpa only [atState, resultSite.end_pc, if_pos hc] using h
    · simpa only [atState, resultSite.end_pc, if_neg hc] using h
  transitionGuard x f := by
    apply transitionGuardSite.lift s _ e (x :: frame f rho)
    have h := run_transitionGuard s (UInt256.ofNat 4584) x f rho hs e.run (valid_190 s e)
    by_cases hc : x.toNat<f.full.toNat
    · simpa only [atState, transitionGuardSite.end_pc, if_pos hc] using h
    · simpa only [atState, transitionGuardSite.end_pc, if_neg hc] using h
  toTail f := by
    apply toTailSite.lift s _ e (frame f rho)
    have hc : (frame f rho).length≤1022 := by simp only [frame, List.length_append, List.length_cons, List.length_nil]; omega
    simpa only [atState] using run_toTail s (UInt256.ofNat 4590) (frame f rho) hc e.run (valid_219 s e)

/-- The scanner's moves; the segment end `clamp size` pushed by the dispatch becomes the frame's `stop` slot. -/
def moves (s : State) (e : Env s) (rest : List UInt256) (hs : rest.length≤989)
    (hactive : s.activeWords = UInt256.ofNat 1) :
    Moves s rest :=
  movesOf s e _ (by omega) hactive (by
    apply initSite.lift s _ e _
    simpa only [atState, initSite.end_pc] using run_init s (UInt256.ofNat 4808) rest hs e.run hactive)

#print axioms moves
#print axioms gasSteps_generic_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
