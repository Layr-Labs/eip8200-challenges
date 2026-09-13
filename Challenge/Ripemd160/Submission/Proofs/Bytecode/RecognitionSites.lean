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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 70).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 70 actual_slice
    (by change 70 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 112 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 70) = UInt256.ofNat 112
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 112) template = UInt256.ofNat 169 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 112 stack) = some t) : GasSteps (atState s 112 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end init

namespace clamp0
abbrev template : List Instr := RecognitionBranchRaw.clampTemplate 178
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 90).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 90 actual_slice
    (by change 90 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 169 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 90) = UInt256.ofNat 169
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 169) template = UInt256.ofNat 175 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 169 stack) = some t) : GasSteps (atState s 169 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end clamp0

namespace reset0
abbrev template : List Instr := RecognitionBranchRaw.resetTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 95).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 95 actual_slice
    (by change 95 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 175 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 95) = UInt256.ofNat 175
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 175) template = UInt256.ofNat 178 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 175 stack) = some t) : GasSteps (atState s 175 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end reset0

namespace pass0
abbrev template : List Instr := RecognitionControlSimplify.passTemplate
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
theorem end_pc : pcAfter (UInt256.ofNat 178) template = UInt256.ofNat 179 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 178 stack) = some t) : GasSteps (atState s 178 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end pass0

namespace pass
abbrev template : List Instr := RecognitionControlSimplify.passTemplate
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
theorem end_pc : pcAfter (UInt256.ofNat 178) template = UInt256.ofNat 179 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 178 stack) = some t) : GasSteps (atState s 178 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end pass

namespace test0
abbrev template : List Instr := RecognitionControlRaw.testTemplate 188
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 99).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 99 actual_slice
    (by change 99 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 179 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 99) = UInt256.ofNat 179
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 179) template = UInt256.ofNat 185 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 179 stack) = some t) : GasSteps (atState s 179 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end test0

namespace skip
abbrev template : List Instr := [.push ⟨1, by decide⟩ (UInt256.ofNat 217), .op .JUMP]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 104).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 104 actual_slice
    (by change 104 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 185 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 104) = UInt256.ofNat 185
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 185) template = UInt256.ofNat 188 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 185 stack) = some t) : GasSteps (atState s 185 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end skip

namespace normal
abbrev template : List Instr := RecognitionFundedBodyRaw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 106).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 106 actual_slice
    (by change 106 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 188 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 106) = UInt256.ofNat 188
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 188) template = UInt256.ofNat 211 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 188 stack) = some t) : GasSteps (atState s 188 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normal

namespace test
abbrev template : List Instr := RecognitionControlRaw.testTemplate 188
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 128).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 128 actual_slice
    (by change 128 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 211 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 128) = UInt256.ofNat 211
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 211) template = UInt256.ofNat 217 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 211 stack) = some t) : GasSteps (atState s 211 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end test

namespace segment
abbrev template : List Instr := RecognitionBranchRaw.segmentTemplate 291
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 133).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 133 actual_slice
    (by change 133 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 217 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 133) = UInt256.ofNat 217
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 217) template = UInt256.ofNat 226 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 217 stack) = some t) : GasSteps (atState s 217 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end segment

namespace boundary
abbrev template : List Instr := RecognitionFundedBodyRaw.boundaryTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 140).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 140 actual_slice
    (by change 140 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 226 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 140) = UInt256.ofNat 226
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 226) template = UInt256.ofNat 279 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 226 stack) = some t) : GasSteps (atState s 226 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end boundary

namespace clamp
abbrev template : List Instr := RecognitionBranchRaw.clampTemplateWith 1 178
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 186).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 186 actual_slice
    (by change 186 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 279 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 186) = UInt256.ofNat 279
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 279) template = UInt256.ofNat 285 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 279 stack) = some t) : GasSteps (atState s 279 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end clamp

namespace reset
abbrev template : List Instr := RecognitionBranchRaw.resetTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 191).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 191 actual_slice
    (by change 191 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 285 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 191) = UInt256.ofNat 285
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 285) template = UInt256.ofNat 288 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 285 stack) = some t) : GasSteps (atState s 285 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end reset

namespace back
/-- Fallthrough backedge: the direct clamp no longer targets this marker. -/
abbrev template : List Instr := [.push ⟨1, by decide⟩ (UInt256.ofNat 178), .op .JUMP]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 194).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 194 actual_slice
    (by change 194 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 288 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 194) = UInt256.ofNat 288
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 288) template = UInt256.ofNat 291 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 288 stack) = some t) : GasSteps (atState s 288 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end back

namespace partialBranch
abbrev template : List Instr := RecognitionBranchRaw.partialTemplate 315
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 196).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 196 actual_slice
    (by change 196 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 291 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 196) = UInt256.ofNat 291
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 291) template = UInt256.ofNat 299 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 291 stack) = some t) : GasSteps (atState s 291 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end partialBranch

namespace partialWord
abbrev template : List Instr := RecognitionControlRaw.partialTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 202).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 202 actual_slice
    (by change 202 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 299 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 202) = UInt256.ofNat 299
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 299) template = UInt256.ofNat 315 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 299 stack) = some t) : GasSteps (atState s 299 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end partialWord

namespace finish
abbrev template : List Instr := RecognitionBranchRaw.finishTemplate 345
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 215).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 215 actual_slice
    (by change 215 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 315 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 215) = UInt256.ofNat 315
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 315) template = UInt256.ofNat 320 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 315 stack) = some t) : GasSteps (atState s 315 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finish

namespace cleanup
abbrev template : List Instr := RecognitionControlSimplify.cleanupTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 233).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 233 actual_slice
    (by change 233 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 345 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 233) = UInt256.ofNat 345
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 345) template = UInt256.ofNat 354 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 345 stack) = some t) : GasSteps (atState s 345 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end cleanup

namespace selector
abbrev template : List Instr := RecognitionSelectorRaw.prefixTemplate (UInt256.ofNat 4953)
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 218).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 218 actual_slice
    (by change 218 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 320 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 218) = UInt256.ofNat 320
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 320) template = UInt256.ofNat 341 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 320 stack) = some t) : GasSteps (atState s 320 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end selector

namespace copy
abbrev template : List Instr := [.op .CODECOPY, .op .MSIZE]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 229).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 229 actual_slice
    (by change 229 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 341 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 229) = UInt256.ofNat 341
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 341) template = UInt256.ofNat 343 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 341 stack) = some t) : GasSteps (atState s 341 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end copy

namespace returned
abbrev template : List Instr := RecognitionSelectorRaw.finish
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 231).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 231 actual_slice
    (by change 231 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 343 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 231) = UInt256.ofNat 343
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 343) template = UInt256.ofNat 345 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 343 stack) = some t) : GasSteps (atState s 343 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end returned

theorem valid_174 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 178).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 98 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 98 = 178 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_175 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 178).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 98 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 98 = 178 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_185 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 188).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 106 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 106 = 188 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_214 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 217).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 133 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 133 = 217 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_291 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 291).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 196 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 196 = 291 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_315 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 315).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 215 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 215 = 315 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_335 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 354).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 242 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 242 = 354 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_342 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 345).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 233 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 233 = 345 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSites
