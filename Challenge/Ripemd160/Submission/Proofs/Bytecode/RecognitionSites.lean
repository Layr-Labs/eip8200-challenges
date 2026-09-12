import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionBranchRaw
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
theorem end_pc : pcAfter (UInt256.ofNat 108) template = UInt256.ofNat 165 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 108 stack) = some t) : GasSteps (atState s 108 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end init

namespace clamp0
abbrev template : List Instr := RecognitionBranchRaw.clampTemplate 174
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 86).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 86 actual_slice
    (by change 86 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 165 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 86) = UInt256.ofNat 165
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 165) template = UInt256.ofNat 171 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 165 stack) = some t) : GasSteps (atState s 165 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end clamp0

namespace reset0
abbrev template : List Instr := RecognitionBranchRaw.resetTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 91).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 91 actual_slice
    (by change 91 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 171 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 91) = UInt256.ofNat 171
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 171) template = UInt256.ofNat 174 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 171 stack) = some t) : GasSteps (atState s 171 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end reset0

namespace pass0
abbrev template : List Instr := [.op .JUMPDEST, .op .JUMPDEST]
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
theorem end_pc : pcAfter (UInt256.ofNat 174) template = UInt256.ofNat 176 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 174 stack) = some t) : GasSteps (atState s 174 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end pass0

namespace pass
abbrev template : List Instr := [.op .JUMPDEST]
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
theorem end_pc : pcAfter (UInt256.ofNat 175) template = UInt256.ofNat 176 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 175 stack) = some t) : GasSteps (atState s 175 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end pass

namespace test0
abbrev template : List Instr := RecognitionControlRaw.testTemplate 185
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 96).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 96 actual_slice
    (by change 96 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 176 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 96) = UInt256.ofNat 176
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 176) template = UInt256.ofNat 182 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 176 stack) = some t) : GasSteps (atState s 176 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end test0

namespace skip
abbrev template : List Instr := [.push ⟨1, by decide⟩ (UInt256.ofNat 214), .op .JUMP]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 101).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 101 actual_slice
    (by change 101 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 182 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 101) = UInt256.ofNat 182
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 182) template = UInt256.ofNat 185 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 182 stack) = some t) : GasSteps (atState s 182 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end skip

namespace normal
abbrev template : List Instr := RecognitionBodyRaw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 103).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 103 actual_slice
    (by change 103 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 185 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 103) = UInt256.ofNat 185
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 185) template = UInt256.ofNat 208 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 185 stack) = some t) : GasSteps (atState s 185 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end normal

namespace test
abbrev template : List Instr := RecognitionControlRaw.testTemplate 185
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 125).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 125 actual_slice
    (by change 125 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 208 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 125) = UInt256.ofNat 208
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 208) template = UInt256.ofNat 214 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 208 stack) = some t) : GasSteps (atState s 208 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end test

namespace segment
abbrev template : List Instr := RecognitionBranchRaw.segmentTemplate 291
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 130).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 130 actual_slice
    (by change 130 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 214 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 130) = UInt256.ofNat 214
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 214) template = UInt256.ofNat 223 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 214 stack) = some t) : GasSteps (atState s 214 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end segment

namespace boundary
abbrev template : List Instr := RecognitionBodyRaw.boundaryTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 137).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 137 actual_slice
    (by change 137 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 223 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 137) = UInt256.ofNat 223
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 223) template = UInt256.ofNat 277 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 223 stack) = some t) : GasSteps (atState s 223 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end boundary

namespace clamp
abbrev template : List Instr := RecognitionBranchRaw.clampTemplateWith 2 287
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 184).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 184 actual_slice
    (by change 184 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 277 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 184) = UInt256.ofNat 277
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 277) template = UInt256.ofNat 284 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 277 stack) = some t) : GasSteps (atState s 277 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end clamp

namespace reset
abbrev template : List Instr := RecognitionBranchRaw.resetTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 189).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 189 actual_slice
    (by change 189 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 284 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 189) = UInt256.ofNat 284
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 284) template = UInt256.ofNat 287 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 284 stack) = some t) : GasSteps (atState s 284 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end reset

namespace back
abbrev template : List Instr := [.op .JUMPDEST, .push ⟨1, by decide⟩ (UInt256.ofNat 175), .op .JUMP]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 192).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 192 actual_slice
    (by change 192 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 287 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 192) = UInt256.ofNat 287
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 287) template = UInt256.ofNat 291 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 287 stack) = some t) : GasSteps (atState s 287 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end back

namespace partialBranch
abbrev template : List Instr := RecognitionBranchRaw.partialTemplate 315
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 195).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 195 actual_slice
    (by change 195 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 291 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 195) = UInt256.ofNat 291
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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 201).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 201 actual_slice
    (by change 201 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 299 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 201) = UInt256.ofNat 299
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 299) template = UInt256.ofNat 315 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 299 stack) = some t) : GasSteps (atState s 299 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end partialWord

namespace finish
abbrev template : List Instr := RecognitionBranchRaw.finishTemplate 4793
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
theorem end_pc : pcAfter (UInt256.ofNat 315) template = UInt256.ofNat 322 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 315 stack) = some t) : GasSteps (atState s 315 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finish

namespace cleanup
abbrev template : List Instr := RecognitionBranchRaw.cleanupTemplate 335
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 219).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 219 actual_slice
    (by change 219 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 322 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 219) = UInt256.ofNat 322
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 322) template = UInt256.ofNat 335 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 322 stack) = some t) : GasSteps (atState s 322 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end cleanup

namespace selector
abbrev template : List Instr := RecognitionSelectorRaw.prefixTemplate (UInt256.ofNat 4819)
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3902).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3902 actual_slice
    (by change 3902 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4793 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3902) = UInt256.ofNat 4793
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4793) template = UInt256.ofNat 4814 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4793 stack) = some t) : GasSteps (atState s 4793 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end selector

namespace copy
abbrev template : List Instr := [.op .CODECOPY, .op .MSIZE]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3914).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3914 actual_slice
    (by change 3914 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4814 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3914) = UInt256.ofNat 4814
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4814) template = UInt256.ofNat 4816 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4814 stack) = some t) : GasSteps (atState s 4814 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end copy

namespace returned
abbrev template : List Instr := RecognitionSelectorRaw.finish
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3916).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3916 actual_slice
    (by change 3916 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4816 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3916) = UInt256.ofNat 4816
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4816) template = UInt256.ofNat 4818 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4816 stack) = some t) : GasSteps (atState s 4816 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end returned

theorem valid_174 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 174).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 94 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 94 = 174 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_175 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 175).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 95 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 95 = 175 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_185 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 185).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 103 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 103 = 185 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_214 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 214).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 130 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 130 = 214 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_287 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 287).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 192 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 192 = 287 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_291 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 291).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 195 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 195 = 291 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_315 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 315).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 214 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 214 = 315 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_335 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 335).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 230 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 230 = 335 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
theorem valid_4796 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4793).toNat = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3902 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3902 = 4793 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simpa only [hp, Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using h
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSites
