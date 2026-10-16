import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedSites
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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3448).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3448 actual_slice
    (by change 3448 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4618 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3448) = UInt256.ofNat 4618
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4618) template = UInt256.ofNat 4691 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4618 stack) = some t) : GasSteps (atState s 4618 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end initSite

namespace firstSite
abbrev template : List Instr := J2Raw.firstTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3457).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3457 actual_slice
    (by change 3457 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4691 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3457) = UInt256.ofNat 4691
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4691) template = UInt256.ofNat 4699 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4691 stack) = some t) : GasSteps (atState s 4691 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end firstSite

namespace normalSite
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3462).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3462 actual_slice
    (by change 3462 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4699 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3462) = UInt256.ofNat 4699
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4699) template = UInt256.ofNat 4717 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4699 stack) = some t) : GasSteps (atState s 4699 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normalSite

namespace normalGuardSite
abbrev template : List Instr := J2Raw.normalGuardTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3480).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3480 actual_slice
    (by change 3480 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4717 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3480) = UInt256.ofNat 4717
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4717) template = UInt256.ofNat 4724 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4717 stack) = some t) : GasSteps (atState s 4717 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normalGuardSite

namespace tailSite
abbrev template : List Instr := J2Raw.tailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3485).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3485 actual_slice
    (by change 3485 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4724 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3485) = UInt256.ofNat 4724
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4724) template = UInt256.ofNat 4729 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4724 stack) = some t) : GasSteps (atState s 4724 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end tailSite

namespace finishSite
abbrev template : List Instr := J2Raw.finishTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3490).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3490 actual_slice
    (by change 3490 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4729 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3490) = UInt256.ofNat 4729
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4729) template = UInt256.ofNat 4736 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4729 stack) = some t) : GasSteps (atState s 4729 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finishSite

namespace finalProjectionSite
abbrev template : List Instr := J2Raw.finalProjectionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3495).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3495 actual_slice
    (by change 3495 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4736 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3495) = UInt256.ofNat 4736
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4736) template = UInt256.ofNat 4744 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4736 stack) = some t) : GasSteps (atState s 4736 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finalProjectionSite



namespace transitionSite
abbrev template : List Instr := J2Raw.transitionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3525).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3525 actual_slice
    (by change 3525 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4779 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3525) = UInt256.ofNat 4779
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4779) template = UInt256.ofNat 4815 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4779 stack) = some t) : GasSteps (atState s 4779 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end transitionSite

-- The old conditional transition guard is gone. Its relocated, unconditional
-- POP/PUSH2/JUMP site is supplied in J2FusedSites.Certificates.




namespace resultSite
abbrev template : List Instr := J2Raw.resultTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3502).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3502 actual_slice
    (by change 3502 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4744 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3502) = UInt256.ofNat 4744
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4744) template = UInt256.ofNat 4748 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4744 stack) = some t) : GasSteps (atState s 4744 stack) t :=
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


theorem valid_190 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4699 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3462 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3462 = 4699 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_219 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4724 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3485 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3485 = 4724 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_298 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4751 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3507 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3507 = 4751 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_341 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4838 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3576 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3576 = 4838 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

def movesOf (c : J2FusedSites.Certificates) (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length≤990)
    (hactive : s.activeWords = UInt256.ofNat 1)
    (hinit : GasSteps (atState s 4618 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
      (atState s 4691 (frame (initResult s.executionEnv.calldata.size) rho))) : Moves s rho where
  init := hinit
  normal f := by
    apply normalSite.lift s _ e (frame f rho)
    simpa only [atState, normalSite.end_pc] using run_normal s (UInt256.ofNat 4699) f rho hs e.run hactive
  tailFinal f hlen hfinal := by
    have g0 : GasSteps (atState s 4724 (frame f rho)) (atState s 4729 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 4724) f rho hs e.run
    have g1 : GasSteps (atState s 4729 (pending s f rho)) (atState s 4736 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_pos hfinal] using
        run_finish s (UInt256.ofNat 4729) f rho hs e.run hlen (valid_298 s e)
    have g2 : GasSteps (atState s 4736 (pending s f rho)) (atState s 4744 (frame (tailResult s f) rho)) := by
      apply finalProjectionSite.lift s _ e (pending s f rho)
      simpa only [atState, finalProjectionSite.end_pc] using
        run_finalProjection s (UInt256.ofNat 4736) f rho hs e.run
    exact g0.trans (g1.trans g2)
  tailBoundary f hlen hfinal _hn256 hmask hshift := by
    have g0 : GasSteps (atState s 4724 (frame f rho)) (atState s 4729 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 4724) f rho hs e.run
    have g1 : GasSteps (atState s 4729 (pending s f rho)) (atState s 4751 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_neg hfinal] using
        run_finish s (UInt256.ofNat 4729) f rho hs e.run hlen (valid_298 s e)
    have g2 := J2FusedSites.longBoundary c s ⟨e.code, e.fork, e.run, e.np⟩
      f rho hs hactive hmask hshift
    exact g0.trans (g1.trans g2)
  fusedBoundary f hlen hfinal h256 := by
    have g0 : GasSteps (atState s 4724 (frame f rho)) (atState s 4729 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 4724) f rho hs e.run
    have g1 : GasSteps (atState s 4729 (pending s f rho)) (atState s 4751 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_neg hfinal] using
        run_finish s (UInt256.ofNat 4729) f rho hs e.run hlen (valid_298 s e)
    have g2 := J2FusedSites.fusedBoundary c s ⟨e.code, e.fork, e.run, e.np⟩
      f rho hs hactive h256 (valid_341 s e)
    exact g0.trans (g1.trans g2)
  transition f hlen := by
    apply transitionSite.lift s _ e (frame f rho)
    simpa only [atState, transitionSite.end_pc] using run_transition s (UInt256.ofNat 4779) f rho hs e.run hlen hactive
  first f hlen := by
    apply firstSite.lift s _ e (frame f rho)
    have h := run_first s (UInt256.ofNat 4691) f rho hs e.run hlen (valid_219 s e)
    by_cases hc : f.len.toNat < 33
    · simpa only [atState, firstSite.end_pc, if_pos hc] using h
    · simpa only [atState, firstSite.end_pc, if_neg hc] using h
  normalGuard f := by
    apply normalGuardSite.lift s _ e (frame f rho)
    have h := run_normalGuard s (UInt256.ofNat 4717) f rho hs e.run (valid_190 s e)
    by_cases hc : f.off.toNat<f.full.toNat
    · simpa only [atState, normalGuardSite.end_pc, if_pos hc] using h
    · simpa only [atState, normalGuardSite.end_pc, if_neg hc] using h
  result f := by
    apply resultSite.lift s _ e (frame f rho)
    have h := run_result s (UInt256.ofNat 4744) f rho hs e.run (valid_341 s e)
    by_cases hc : f.acc.toNat=0
    · simpa only [atState, resultSite.end_pc, if_pos hc] using h
    · simpa only [atState, resultSite.end_pc, if_neg hc] using h
  transitionGuard x f :=
    J2FusedSites.gasSteps_transitionGuard c s ⟨e.code, e.fork, e.run, e.np⟩
      x f rho hs (valid_190 s e)

/-- The scanner's moves; the segment end `clamp size` pushed by the dispatch becomes the frame's `stop` slot. -/
def moves (c : J2FusedSites.Certificates) (s : State) (e : Env s) (rest : List UInt256) (hs : rest.length≤989)
    (hactive : s.activeWords = UInt256.ofNat 1) :
    Moves s rest :=
  movesOf c s e _ (by omega) hactive (by
    apply initSite.lift s _ e _
    simpa only [atState, initSite.end_pc] using run_init s (UInt256.ofNat 4618) rest hs e.run hactive)

#print axioms moves
#print axioms gasSteps_generic_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
