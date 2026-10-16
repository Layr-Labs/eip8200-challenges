import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open J2Raw J2Moves J2FusedRaw StackRoundTrace StackRoundTemplate

structure Env (s : State) : Prop where
  code : s.executionEnv.code = Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

/-- Only artifact-layout facts belong here. No input-dependent or semantic
assumptions are part of the relocation certificate. -/
structure Site (template : List Instr) (pc : Nat) where
  site : GenericRoundSite Artifact.submissionArtifact .Osaka template
  pc_eq : site.startPC = UInt256.ofNat pc

structure Certificates where
  branch : Site branchTemplate 4888
  predicate : Site predicateTemplate fusedPC
  projection : Site projectionTemplate non256PC
  finish : Site fullReturnTemplate fusedReturnPC
  non256_valid : Decode.isValidJumpDest Artifact.submissionArtifact.code non256PC = true
  projection_end : pcAfter (UInt256.ofNat non256PC) projectionTemplate = UInt256.ofNat 4916

private theorem code_bound : Artifact.submissionArtifact.code.size < 2^256 := by
  change submissionBytecode.size < 2^256
  rw [referenceBytecode_size]
  decide

namespace branchSite
abbrev template : List Instr := branchTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3551).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3551 actual_slice
    (by change 3551 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4888 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3551) = UInt256.ofNat 4888
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
end branchSite

namespace predicateSite
abbrev template : List Instr := predicateTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3557).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3557 actual_slice
    (by change 3557 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4896 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3557) = UInt256.ofNat 4896
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
end predicateSite

namespace projectionSite
abbrev template : List Instr := projectionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3565).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3565 actual_slice
    (by change 3565 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4911 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3565) = UInt256.ofNat 4911
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
end projectionSite

namespace finishSite
abbrev template : List Instr := fullReturnTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3562).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3562 actual_slice
    (by change 3562 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4908 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3562) = UInt256.ofNat 4908
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
end finishSite

def certificates : Certificates where
  branch := ⟨branchSite.site, branchSite.site_pc⟩
  predicate := ⟨predicateSite.site, predicateSite.site_pc⟩
  projection := ⟨projectionSite.site, projectionSite.site_pc⟩
  finish := ⟨finishSite.site, finishSite.site_pc⟩
  non256_valid := by
    have h := Artifact.submissionArtifact.isValidJumpDest_index 3565 (by rfl)
    have hp : Artifact.submissionArtifact.instructionPC 3565 = 4911 := by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
    simpa only [J2Moves.non256PC, hp] using h
  projection_end := by decide

private def lift {template : List Instr} {pc : Nat} (site : Site template pc)
    (s t : State) (e : Env s) (stack : List UInt256)
    (hform : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction)
    (h : runInstrSeq template (atState s pc stack) = some t) :
    GasSteps (atState s pc stack) t :=
  RecognitionLift.gasSteps_of_raw site.site _ _ e.code e.fork e.run e.np
    site.pc_eq.symm hform h

private def branch (c : Certificates) (s : State) (e : Env s)
    (stack : List UInt256) (hs : stack.length ≤ 1018)
    (hactive : s.activeWords = UInt256.ofNat 1) :
    GasSteps (atState s 4888 stack)
      (atState s (if UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) 32 = 0
        then fusedPC else non256PC) stack) := by
  apply lift c.branch s _ e stack (RecognitionLift.advancesAll_sound _ (by decide))
  have hv : Decode.isValidJumpDest s.executionEnv.code non256PC = true := by
    rw [e.code]; exact c.non256_valid
  have h := run_branch s (UInt256.ofNat 4888) stack hs e.run hactive hv
  by_cases hm : UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) 32 = 0
  all_goals simpa only [atState, hm, if_true, if_false, J2Moves.non256PC,
    show pcAfter (UInt256.ofNat 4888) branchTemplate = UInt256.ofNat fusedPC from by decide] using h

def longBoundary (c : Certificates) (s : State) (e : Env s)
    (f : J2Raw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990)
    (hactive : s.activeWords = UInt256.ofNat 1)
    (hmask : UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) 32 ≠ 0)
    (hboundary : f.stop.toNat < f.len.toNat) :
    GasSteps (atState s 4888 (pending s f rho)) (atState s 4916 (frame (tailResult s f) rho)) := by
  have gb := branch c s e (pending s f rho)
    (by simp [pending, frame]; omega) hactive
  rw [if_neg hmask] at gb
  apply gb.trans
  apply lift c.projection s _ e _ (RecognitionLift.advancesAll_sound _ (by decide))
  have h := run_boundaryProjection s (UInt256.ofNat non256PC) f rho hs e.run hboundary
  change runInstrSeq projectionTemplate _ = some {s with
    pc := pcAfter (UInt256.ofNat non256PC) projectionTemplate, stack := frame (tailResult s f) rho} at h
  rw [c.projection_end] at h
  exact h

def fusedBoundary (c : Certificates) (s : State) (e : Env s)
    (f : J2Raw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990)
    (hactive : s.activeWords = UInt256.ofNat 1) (h256 : s.executionEnv.calldata.size = 256)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4565 = true) :
    GasSteps (atState s 4888 (pending s f rho))
      (atState s (if (fusedAcc s f).toNat = 0 then fusedReturnPC else 4565) (finishRest f rho)) := by
  have gb := branch c s e (pending s f rho)
    (by simp [pending, frame]; omega) hactive
  have hmask : UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) 32 = 0 := by
    rw [h256]; decide
  rw [if_pos hmask] at gb
  apply gb.trans
  apply lift c.predicate s _ e _ (RecognitionLift.advancesAll_sound _ (by decide))
  have h := run_predicate s (UInt256.ofNat fusedPC) f rho hs e.run hvalid
  by_cases hz : (fusedAcc s f).toNat = 0
  all_goals simpa only [atState, hz, if_true, if_false,
    show pcAfter (UInt256.ofNat fusedPC) predicateTemplate = UInt256.ofNat fusedReturnPC from by decide] using h

/-- Direct return with a residual frame, using the same prepared-memory invariant. -/
def gasSteps_return (c : Certificates) (input : ByteArray) (saved rho : List UInt256)
    (hc : rho.length ≤ 990) :
    GasSteps (atState (EarlySerializeReturn.prepared input saved) fusedReturnPC rho)
      (J2FusedCorrect.output input rho) := by
  let s := EarlySerializeReturn.prepared input saved
  have e : Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  apply lift c.finish s _ e rho (RecognitionLift.advancesAll_sound _ (by decide))
  have h := run_fullReturn s (UInt256.ofNat fusedReturnPC) rho hc rfl rfl
  have hout : RecognitionSelectorRaw.returned s
      (UInt256.ofNat fusedReturnPC + UInt256.ofNat 1) rho = J2FusedCorrect.output input rho := by
    change RecognitionSelectorRaw.returned (EarlySerializeReturn.prepared input saved)
      (UInt256.ofNat fusedReturnPC + UInt256.ofNat 1) rho = _
    unfold J2FusedCorrect.output RecognitionSelectorRaw.returned
    have hpc : UInt256.ofNat fusedReturnPC + UInt256.ofNat 1 = UInt256.ofNat (fusedReturnPC+1) := by decide
    simp only [hpc, EarlySerializeReturn.prepared, RecognitionSelectorResult.copied,
      EarlySerializeReturn.beforeCopy, atState, EarlySerializeReturn.base, State.activeWordsAfterUInt256]
  exact hout ▸ h


#print axioms longBoundary
#print axioms fusedBoundary
#print axioms gasSteps_return
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedSites
