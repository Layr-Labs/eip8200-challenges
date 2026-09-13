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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 72).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 72 actual_slice
    (by change 72 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 116 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 72) = UInt256.ofNat 116
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 116) template = UInt256.ofNat 173 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 116 stack) = some t) : GasSteps (atState s 116 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end init

namespace clamp0
abbrev template : List Instr := RecognitionBranchRaw.clampTemplate 182
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 92).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 92 actual_slice
    (by change 92 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 173 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 92) = UInt256.ofNat 173
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 173) template = UInt256.ofNat 179 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 173 stack) = some t) : GasSteps (atState s 173 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end clamp0

namespace reset0
abbrev template : List Instr := RecognitionBranchRaw.resetTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 97).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 97 actual_slice
    (by change 97 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 179 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 97) = UInt256.ofNat 179
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 179) template = UInt256.ofNat 182 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 179 stack) = some t) : GasSteps (atState s 179 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end reset0

namespace pass0
abbrev template : List Instr := RecognitionControlSimplify.passTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 100).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 100 actual_slice
    (by change 100 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 182 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 100) = UInt256.ofNat 182
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 182) template = UInt256.ofNat 183 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 182 stack) = some t) : GasSteps (atState s 182 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end pass0

namespace pass
abbrev template : List Instr := RecognitionControlSimplify.passTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 100).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 100 actual_slice
    (by change 100 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 182 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 100) = UInt256.ofNat 182
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 182) template = UInt256.ofNat 183 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 182 stack) = some t) : GasSteps (atState s 182 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end pass

namespace test0
abbrev template : List Instr := RecognitionControlRaw.testTemplate 192
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 101).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 101 actual_slice
    (by change 101 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 183 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 101) = UInt256.ofNat 183
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 183) template = UInt256.ofNat 189 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 183 stack) = some t) : GasSteps (atState s 183 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end test0

namespace skip
abbrev template : List Instr := [.push ⟨1, by decide⟩ (UInt256.ofNat 221), .op .JUMP]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 106).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 106 actual_slice
    (by change 106 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 189 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 106) = UInt256.ofNat 189
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 189) template = UInt256.ofNat 192 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 189 stack) = some t) : GasSteps (atState s 189 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end skip

namespace normal
abbrev template : List Instr := RecognitionFundedBodyRaw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 108).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 108 actual_slice
    (by change 108 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 192 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 108) = UInt256.ofNat 192
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 192) template = UInt256.ofNat 215 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 192 stack) = some t) : GasSteps (atState s 192 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normal

namespace test
abbrev template : List Instr := RecognitionControlRaw.testTemplate 192
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 130).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 130 actual_slice
    (by change 130 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 215 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 130) = UInt256.ofNat 215
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 215) template = UInt256.ofNat 221 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 215 stack) = some t) : GasSteps (atState s 215 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end test

namespace segment
abbrev template : List Instr := RecognitionBranchRaw.segmentTemplate 296
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 135).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 135 actual_slice
    (by change 135 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 221 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 135) = UInt256.ofNat 221
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 221) template = UInt256.ofNat 230 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 221 stack) = some t) : GasSteps (atState s 221 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end segment

namespace boundary
abbrev template : List Instr := RecognitionFundedBodyRaw.boundaryTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 142).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 142 actual_slice
    (by change 142 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 230 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 142) = UInt256.ofNat 230
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 230) template = UInt256.ofNat 283 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 230 stack) = some t) : GasSteps (atState s 230 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end boundary

namespace clamp
abbrev template : List Instr := RecognitionBranchRaw.clampTemplateWith 1 182
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 188).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 188 actual_slice
    (by change 188 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 283 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 188) = UInt256.ofNat 283
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 283) template = UInt256.ofNat 289 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 283 stack) = some t) : GasSteps (atState s 283 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end clamp

namespace reset
abbrev template : List Instr := RecognitionBranchRaw.resetTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 193).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 193 actual_slice
    (by change 193 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 289 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 193) = UInt256.ofNat 289
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 289) template = UInt256.ofNat 292 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 289 stack) = some t) : GasSteps (atState s 289 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end reset

namespace back
/-- Fallthrough backedge: the direct clamp no longer targets this marker. -/
abbrev template : List Instr := [.push ⟨2, by decide⟩ (UInt256.ofNat 182), .op .JUMP]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 196).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 196 actual_slice
    (by change 196 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 292 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 196) = UInt256.ofNat 292
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 292) template = UInt256.ofNat 296 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 292 stack) = some t) : GasSteps (atState s 292 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end back

namespace partialBranch
abbrev template : List Instr := RecognitionBranchRaw.partialTemplate 320
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 198).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 198 actual_slice
    (by change 198 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 296 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 198) = UInt256.ofNat 296
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 296) template = UInt256.ofNat 304 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 296 stack) = some t) : GasSteps (atState s 296 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end partialBranch

namespace partialWord
abbrev template : List Instr := RecognitionControlRaw.partialTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 204).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 204 actual_slice
    (by change 204 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 304 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 204) = UInt256.ofNat 304
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 304) template = UInt256.ofNat 320 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 304 stack) = some t) : GasSteps (atState s 304 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end partialWord

namespace finish
abbrev template : List Instr := RecognitionBranchRaw.finishTemplate 349
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 217).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 217 actual_slice
    (by change 217 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 320 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 217) = UInt256.ofNat 320
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 320) template = UInt256.ofNat 325 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 320 stack) = some t) : GasSteps (atState s 320 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finish

namespace cleanup
abbrev template : List Instr := RecognitionControlSimplify.cleanupTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 235).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 235 actual_slice
    (by change 235 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 349 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 235) = UInt256.ofNat 349
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 349) template = UInt256.ofNat 358 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 349 stack) = some t) : GasSteps (atState s 349 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end cleanup

namespace selector
abbrev template : List Instr := RecognitionSelectorRaw.prefixTemplate (UInt256.ofNat 4984)
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 220).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 220 actual_slice
    (by change 220 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 325 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 220) = UInt256.ofNat 325
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 325) template = UInt256.ofNat 345 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 325 stack) = some t) : GasSteps (atState s 325 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end selector

namespace copy
abbrev template : List Instr := [.op .CODECOPY, .op .MSIZE]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 231).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 231 actual_slice
    (by change 231 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 345 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 231) = UInt256.ofNat 345
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 345) template = UInt256.ofNat 347 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 345 stack) = some t) : GasSteps (atState s 345 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end copy

namespace returned
abbrev template : List Instr := RecognitionSelectorRaw.finish
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 233).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 233 actual_slice
    (by change 233 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 347 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 233) = UInt256.ofNat 347
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 347) template = UInt256.ofNat 349 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 347 stack) = some t) : GasSteps (atState s 347 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end returned

theorem valid_174 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 182).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 100 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 100 = 182 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_175 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 182).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 100 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 100 = 182 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_185 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 192).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 108 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 108 = 192 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_214 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 221).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 135 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 135 = 221 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_291 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 296).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 198 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 198 = 296 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_315 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 320).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 217 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 217 = 320 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_335 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 358).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 244 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 244 = 358 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_342 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 349).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 235 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 235 = 349 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSites
