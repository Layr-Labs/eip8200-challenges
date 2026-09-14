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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 69).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 69 actual_slice
    (by change 69 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 111 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 69) = UInt256.ofNat 111
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 111) template = UInt256.ofNat 168 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 111 stack) = some t) : GasSteps (atState s 111 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end init

namespace clamp0
abbrev template : List Instr := RecognitionBranchRaw.clampTemplate 177
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 89).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 89 actual_slice
    (by change 89 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 168 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 89) = UInt256.ofNat 168
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 168) template = UInt256.ofNat 174 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 168 stack) = some t) : GasSteps (atState s 168 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end clamp0

namespace reset0
abbrev template : List Instr := RecognitionBranchRaw.resetTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 94).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 94 actual_slice
    (by change 94 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 174 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 94) = UInt256.ofNat 174
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 174) template = UInt256.ofNat 177 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 174 stack) = some t) : GasSteps (atState s 174 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end reset0

namespace pass0
abbrev template : List Instr := RecognitionControlSimplify.passTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 97).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 97 actual_slice
    (by change 97 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 177 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 97) = UInt256.ofNat 177
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 177) template = UInt256.ofNat 178 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 177 stack) = some t) : GasSteps (atState s 177 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end pass0

namespace pass
abbrev template : List Instr := RecognitionControlSimplify.passTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 97).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 97 actual_slice
    (by change 97 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 177 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 97) = UInt256.ofNat 177
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 177) template = UInt256.ofNat 178 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 177 stack) = some t) : GasSteps (atState s 177 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end pass

namespace test0
abbrev template : List Instr := RecognitionControlRaw.headTemplate 213
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 98).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 98 actual_slice
    (by change 98 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 178 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 98) = UInt256.ofNat 178
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 178) template = UInt256.ofNat 184 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 178 stack) = some t) : GasSteps (atState s 178 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end test0


namespace normal
abbrev template : List Instr := RecognitionFundedBodyRaw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 103).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 103 actual_slice
    (by change 103 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 184 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 103) = UInt256.ofNat 184
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 184) template = UInt256.ofNat 207 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 184 stack) = some t) : GasSteps (atState s 184 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normal

namespace test
abbrev template : List Instr := RecognitionControlRaw.testTemplate 184
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 125).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 125 actual_slice
    (by change 125 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 207 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 125) = UInt256.ofNat 207
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 207) template = UInt256.ofNat 213 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 207 stack) = some t) : GasSteps (atState s 207 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end test

namespace segment
abbrev template : List Instr := RecognitionBranchRaw.segmentTemplate 286
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 130).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 130 actual_slice
    (by change 130 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 213 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 130) = UInt256.ofNat 213
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 213) template = UInt256.ofNat 221 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 213 stack) = some t) : GasSteps (atState s 213 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end segment

namespace boundary
abbrev template : List Instr := RecognitionFundedBodyRaw.boundaryTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 136).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 136 actual_slice
    (by change 136 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 221 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 136) = UInt256.ofNat 221
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 221) template = UInt256.ofNat 274 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 221 stack) = some t) : GasSteps (atState s 221 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end boundary

namespace clamp
abbrev template : List Instr := RecognitionBranchRaw.clampTemplateWith 1 177
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 182).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 182 actual_slice
    (by change 182 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 274 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 182) = UInt256.ofNat 274
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 274) template = UInt256.ofNat 280 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 274 stack) = some t) : GasSteps (atState s 274 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end clamp

namespace reset
abbrev template : List Instr := RecognitionBranchRaw.resetTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 187).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 187 actual_slice
    (by change 187 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 280 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 187) = UInt256.ofNat 280
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 280) template = UInt256.ofNat 283 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 280 stack) = some t) : GasSteps (atState s 280 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end reset

namespace back
/-- Fallthrough backedge: the direct clamp no longer targets this marker. -/
abbrev template : List Instr := [.push ⟨1, by decide⟩ (UInt256.ofNat 177), .op .JUMP]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 190).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 190 actual_slice
    (by change 190 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 283 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 190) = UInt256.ofNat 283
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 283) template = UInt256.ofNat 286 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 283 stack) = some t) : GasSteps (atState s 283 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end back

namespace partialBranch
abbrev template : List Instr := RecognitionBranchRaw.partialTemplate 310
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 192).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 192 actual_slice
    (by change 192 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 286 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 192) = UInt256.ofNat 286
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 286) template = UInt256.ofNat 294 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 286 stack) = some t) : GasSteps (atState s 286 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end partialBranch

namespace partialWord
abbrev template : List Instr := RecognitionControlRaw.partialTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 198).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 198 actual_slice
    (by change 198 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 294 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 198) = UInt256.ofNat 294
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 294) template = UInt256.ofNat 310 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 294 stack) = some t) : GasSteps (atState s 294 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end partialWord

namespace finish
abbrev template : List Instr := RecognitionBranchRaw.finishTemplate 342
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 211).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 211 actual_slice
    (by change 211 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 310 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 211) = UInt256.ofNat 310
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 310) template = UInt256.ofNat 315 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 310 stack) = some t) : GasSteps (atState s 310 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finish

namespace cleanup
abbrev template : List Instr := RecognitionControlSimplify.cleanupTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 229).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 229 actual_slice
    (by change 229 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 342 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 229) = UInt256.ofNat 342
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 342) template = UInt256.ofNat 351 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 342 stack) = some t) : GasSteps (atState s 342 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end cleanup

namespace selector
abbrev template : List Instr := RecognitionSelectorRaw.prefixTemplate (UInt256.ofNat 4953)
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 214).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 214 actual_slice
    (by change 214 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 315 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 214) = UInt256.ofNat 315
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 315) template = UInt256.ofNat 338 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 315 stack) = some t) : GasSteps (atState s 315 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end selector

namespace copy
abbrev template : List Instr := [.op .CODECOPY, .op .MSIZE]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 225).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 225 actual_slice
    (by change 225 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 338 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 225) = UInt256.ofNat 338
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 338) template = UInt256.ofNat 340 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 338 stack) = some t) : GasSteps (atState s 338 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end copy

namespace returned
abbrev template : List Instr := RecognitionSelectorRaw.finish
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 227).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 227 actual_slice
    (by change 227 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 340 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 227) = UInt256.ofNat 340
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 340) template = UInt256.ofNat 342 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 340 stack) = some t) : GasSteps (atState s 340 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end returned

theorem valid_174 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 177).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 97 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 97 = 177 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_175 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 177).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 97 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 97 = 177 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_185 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 184).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 103 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 103 = 184 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_214 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 213).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 130 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 130 = 213 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_291 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 286).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 192 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 192 = 286 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_315 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 310).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 211 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 211 = 310 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_335 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 351).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 238 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 238 = 351 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_342 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 342).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 229 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 229 = 342 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSites
