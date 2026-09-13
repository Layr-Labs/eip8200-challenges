import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionFundedBodyRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate
structure Env (s : State) : Prop where
  code : s.executionEnv.code = Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def atState (s : State) (pc : Nat) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := stack}

namespace init
abbrev template : List Instr := RecognitionControlRaw.initBodyTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 66).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 66 actual_slice
    (by change 66 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 108 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 66) = UInt256.ofNat 108
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 108) template = UInt256.ofNat 312 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 108 stack) = some t) : GasSteps (atState s 108 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end init

namespace clamp0
abbrev template : List Instr := RecognitionBranchRaw.clampTemplate 322
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 77).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 77 actual_slice
    (by change 77 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 312 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 77) = UInt256.ofNat 312
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 312) template = UInt256.ofNat 319 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 312 stack) = some t) : GasSteps (atState s 312 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end clamp0

namespace reset0
abbrev template : List Instr := RecognitionBranchRaw.resetTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 82).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 82 actual_slice
    (by change 82 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 319 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 82) = UInt256.ofNat 319
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 319) template = UInt256.ofNat 322 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 319 stack) = some t) : GasSteps (atState s 319 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end reset0

namespace pass0
abbrev template : List Instr := RecognitionControlSimplify.passTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 85).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 85 actual_slice
    (by change 85 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 322 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 85) = UInt256.ofNat 322
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 322) template = UInt256.ofNat 323 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 322 stack) = some t) : GasSteps (atState s 322 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end pass0

namespace pass
abbrev template : List Instr := RecognitionControlSimplify.passTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 85).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 85 actual_slice
    (by change 85 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 322 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 85) = UInt256.ofNat 322
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 322) template = UInt256.ofNat 323 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 322 stack) = some t) : GasSteps (atState s 322 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end pass

namespace test0
abbrev template : List Instr := RecognitionControlRaw.testTemplate 334
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 86).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 86 actual_slice
    (by change 86 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 323 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 86) = UInt256.ofNat 323
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 323) template = UInt256.ofNat 330 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 323 stack) = some t) : GasSteps (atState s 323 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end test0

namespace skip
abbrev template : List Instr := [.push ⟨2, by decide⟩ (UInt256.ofNat 364), .op .JUMP]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 91).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 91 actual_slice
    (by change 91 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 330 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 91) = UInt256.ofNat 330
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 330) template = UInt256.ofNat 334 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 330 stack) = some t) : GasSteps (atState s 330 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end skip

namespace normal
abbrev template : List Instr := RecognitionFundedBodyRaw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 93).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 93 actual_slice
    (by change 93 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 334 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 93) = UInt256.ofNat 334
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 334) template = UInt256.ofNat 357 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 334 stack) = some t) : GasSteps (atState s 334 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normal

namespace test
abbrev template : List Instr := RecognitionControlRaw.testTemplate 334
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 115).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 115 actual_slice
    (by change 115 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 357 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 115) = UInt256.ofNat 357
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 357) template = UInt256.ofNat 364 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 357 stack) = some t) : GasSteps (atState s 357 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end test

namespace segment
abbrev template : List Instr := RecognitionBranchRaw.segmentTemplate 440
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 120).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 120 actual_slice
    (by change 120 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 364 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 120) = UInt256.ofNat 364
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 364) template = UInt256.ofNat 373 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 364 stack) = some t) : GasSteps (atState s 364 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end segment

namespace boundary
abbrev template : List Instr := RecognitionFundedBodyRaw.boundaryTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 127).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 127 actual_slice
    (by change 127 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 373 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 127) = UInt256.ofNat 373
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 373) template = UInt256.ofNat 426 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 373 stack) = some t) : GasSteps (atState s 373 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end boundary

namespace clamp
abbrev template : List Instr := RecognitionBranchRaw.clampTemplateWith 2 322
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 173).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 173 actual_slice
    (by change 173 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 426 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 173) = UInt256.ofNat 426
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 426) template = UInt256.ofNat 433 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 426 stack) = some t) : GasSteps (atState s 426 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end clamp

namespace reset
abbrev template : List Instr := RecognitionBranchRaw.resetTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 178).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 178 actual_slice
    (by change 178 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 433 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 178) = UInt256.ofNat 433
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 433) template = UInt256.ofNat 436 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 433 stack) = some t) : GasSteps (atState s 433 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end reset

namespace back
/-- Fallthrough backedge: the direct clamp no longer targets this marker. -/
abbrev template : List Instr := [.push ⟨2, by decide⟩ (UInt256.ofNat 322), .op .JUMP]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 181).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 181 actual_slice
    (by change 181 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 436 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 181) = UInt256.ofNat 436
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 436) template = UInt256.ofNat 440 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 436 stack) = some t) : GasSteps (atState s 436 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end back

namespace partialBranch
abbrev template : List Instr := RecognitionBranchRaw.partialTemplate 464
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 183).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 183 actual_slice
    (by change 183 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 440 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 183) = UInt256.ofNat 440
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 440) template = UInt256.ofNat 448 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 440 stack) = some t) : GasSteps (atState s 440 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end partialBranch

namespace partialWord
abbrev template : List Instr := RecognitionControlRaw.partialTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 189).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 189 actual_slice
    (by change 189 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 448 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 189) = UInt256.ofNat 448
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 448) template = UInt256.ofNat 464 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 448 stack) = some t) : GasSteps (atState s 448 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end partialWord

namespace finish
abbrev template : List Instr := RecognitionBranchRaw.finishTemplate 488
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 202).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 202 actual_slice
    (by change 202 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 464 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 202) = UInt256.ofNat 464
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 464) template = UInt256.ofNat 469 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 464 stack) = some t) : GasSteps (atState s 464 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finish

namespace cleanup
abbrev template : List Instr := RecognitionControlSimplify.cleanupTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 218).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 218 actual_slice
    (by change 218 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 488 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 218) = UInt256.ofNat 488
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 488) template = UInt256.ofNat 497 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 488 stack) = some t) : GasSteps (atState s 488 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end cleanup

namespace selector
abbrev template : List Instr := RecognitionSelectorRaw.prefixTemplate (UInt256.ofNat 5456)
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 205).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 205 actual_slice
    (by change 205 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 469 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 205) = UInt256.ofNat 469
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 469) template = UInt256.ofNat 484 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 469 stack) = some t) : GasSteps (atState s 469 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end selector

namespace copy
abbrev template : List Instr := [.op .CODECOPY, .op .MSIZE]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 214).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 214 actual_slice
    (by change 214 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 484 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 214) = UInt256.ofNat 484
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 484) template = UInt256.ofNat 486 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 484 stack) = some t) : GasSteps (atState s 484 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end copy

namespace returned
abbrev template : List Instr := RecognitionSelectorRaw.finish
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 216).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 216 actual_slice
    (by change 216 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 486 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 216) = UInt256.ofNat 486
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 486) template = UInt256.ofNat 488 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 486 stack) = some t) : GasSteps (atState s 486 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end returned

theorem valid_174 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 322).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 85 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 85 = 322 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_175 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 322).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 85 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 85 = 322 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_185 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 334).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 93 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 93 = 334 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_214 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 364).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 120 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 120 = 364 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_291 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 440).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 183 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 183 = 440 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_315 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 464).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 202 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 202 = 464 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_335 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 497).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 227 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 227 = 497 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_342 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 488).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 218 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 218 = 488 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSites
