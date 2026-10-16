import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedSites
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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3535).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3535 actual_slice
    (by change 3535 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4804 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3535) = UInt256.ofNat 4804
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4804) template = UInt256.ofNat 4877 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4804 stack) = some t) : GasSteps (atState s 4804 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end initSite

namespace dispatch0Site
abbrev template : List Instr := J2Raw.dispatch0Template
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3544).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3544 actual_slice
    (by change 3544 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4877 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3544) = UInt256.ofNat 4877
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4877 stack) = some t) : GasSteps (atState s 4877 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end dispatch0Site

namespace block0Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3611).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3611 actual_slice
    (by change 3611 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4964 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3611) = UInt256.ofNat 4964
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4964) template = UInt256.ofNat 4982 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4964 stack) = some t) : GasSteps (atState s 4964 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block0Site

namespace block1Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3629).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3629 actual_slice
    (by change 3629 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4982 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3629) = UInt256.ofNat 4982
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4982) template = UInt256.ofNat 5000 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4982 stack) = some t) : GasSteps (atState s 4982 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block1Site

namespace block2Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3647).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3647 actual_slice
    (by change 3647 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5000 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3647) = UInt256.ofNat 5000
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5000) template = UInt256.ofNat 5018 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5000 stack) = some t) : GasSteps (atState s 5000 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block2Site

namespace block3Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3665).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3665 actual_slice
    (by change 3665 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5018 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3665) = UInt256.ofNat 5018
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5018) template = UInt256.ofNat 5036 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5018 stack) = some t) : GasSteps (atState s 5018 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block3Site

namespace block4Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3683).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3683 actual_slice
    (by change 3683 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5036 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3683) = UInt256.ofNat 5036
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5036) template = UInt256.ofNat 5054 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5036 stack) = some t) : GasSteps (atState s 5036 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block4Site

namespace block5Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3701).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3701 actual_slice
    (by change 3701 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5054 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3701) = UInt256.ofNat 5054
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5054) template = UInt256.ofNat 5072 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5054 stack) = some t) : GasSteps (atState s 5054 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block5Site

namespace block6Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3719).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3719 actual_slice
    (by change 3719 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5072 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3719) = UInt256.ofNat 5072
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5072) template = UInt256.ofNat 5090 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5072 stack) = some t) : GasSteps (atState s 5072 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block6Site

namespace tailSite
abbrev template : List Instr := J2Raw.tailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3737).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3737 actual_slice
    (by change 3737 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5090 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3737) = UInt256.ofNat 5090
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5090) template = UInt256.ofNat 5095 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5090 stack) = some t) : GasSteps (atState s 5090 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end tailSite

namespace finishSite
abbrev template : List Instr := J2Raw.finishTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3742).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3742 actual_slice
    (by change 3742 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5095 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3742) = UInt256.ofNat 5095
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5095) template = UInt256.ofNat 5102 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5095 stack) = some t) : GasSteps (atState s 5095 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finishSite

namespace finalProjectionSite
abbrev template : List Instr := J2Raw.finalProjectionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3747).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3747 actual_slice
    (by change 3747 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5102 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3747) = UInt256.ofNat 5102
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5102) template = UInt256.ofNat 5110 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5102 stack) = some t) : GasSteps (atState s 5102 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finalProjectionSite

namespace resultSite
abbrev template : List Instr := J2Raw.resultTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3754).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3754 actual_slice
    (by change 3754 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5110 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3754) = UInt256.ofNat 5110
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5110) template = UInt256.ofNat 5114 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5110 stack) = some t) : GasSteps (atState s 5110 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end resultSite

namespace boundaryProjectionSite
abbrev template : List Instr := J2Raw.boundaryProjectionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3568).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3568 actual_slice
    (by change 3568 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4914 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3568) = UInt256.ofNat 4914
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4914) template = UInt256.ofNat 4919 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4914 stack) = some t) : GasSteps (atState s 4914 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end boundaryProjectionSite

namespace transitionSite
abbrev template : List Instr := J2Raw.transitionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3572).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3572 actual_slice
    (by change 3572 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4919 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3572) = UInt256.ofNat 4919
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4919) template = UInt256.ofNat 4955 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4919 stack) = some t) : GasSteps (atState s 4919 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end transitionSite

namespace dispatch1Site
abbrev template : List Instr := J2Raw.dispatch1Template
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3605).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3605 actual_slice
    (by change 3605 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4955 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3605) = UInt256.ofNat 4955
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4955 stack) = some t) : GasSteps (atState s 4955 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end dispatch1Site

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


theorem valid_block0 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4964 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3611 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3611 = 4964 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block1 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4982 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3629 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3629 = 4982 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block2 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5000 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3647 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3647 = 5000 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block3 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5018 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3665 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3665 = 5018 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block4 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5036 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3683 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3683 = 5036 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block5 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5054 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3701 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3701 = 5054 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block6 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5072 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3719 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3719 = 5072 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block7 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5090 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3737 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3737 = 5090 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_boundary (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4891 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3554 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3554 = 4891 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_miss (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4565 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3412 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3412 = 4565 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block (s : State) (e : Env s) (j : Nat) (hj : j ≤ 7) :
    Decode.isValidJumpDest s.executionEnv.code (blockPC j) = true := by
  interval_cases j
  · exact valid_block0 s e
  · exact valid_block1 s e
  · exact valid_block2 s e
  · exact valid_block3 s e
  · exact valid_block4 s e
  · exact valid_block5 s e
  · exact valid_block6 s e
  · exact valid_block7 s e

theorem valid_target (s : State) (e : Env s) (x full : UInt256) (j : Nat) (hj : j ≤ 7)
    (ht : dispatchTarget x full = UInt256.ofNat (blockPC j)) :
    Decode.isValidJumpDest s.executionEnv.code (dispatchTarget x full).toNat = true := by
  have hlt : blockPC j < 2 ^ 256 := by unfold blockPC; omega
  rw [ht, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact valid_block s e j hj

def normalAt (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length≤990)
    (hactive : s.activeWords = UInt256.ofNat 1) (j : Nat) (hj : j < 7) (f : J2Raw.Frame) :
    GasSteps (atState s (blockPC j) (frame f rho)) (atState s (blockPC (j+1)) (frame (normalResult s f) rho)) := by
  have h := fun pc => run_normal s pc f rho hs e.run hactive
  interval_cases j
  · show GasSteps (atState s 4964 (frame f rho)) (atState s 4982 (frame (normalResult s f) rho))
    apply block0Site.lift s _ e (frame f rho)
    simpa only [atState, block0Site.end_pc] using h (UInt256.ofNat 4964)
  · show GasSteps (atState s 4982 (frame f rho)) (atState s 5000 (frame (normalResult s f) rho))
    apply block1Site.lift s _ e (frame f rho)
    simpa only [atState, block1Site.end_pc] using h (UInt256.ofNat 4982)
  · show GasSteps (atState s 5000 (frame f rho)) (atState s 5018 (frame (normalResult s f) rho))
    apply block2Site.lift s _ e (frame f rho)
    simpa only [atState, block2Site.end_pc] using h (UInt256.ofNat 5000)
  · show GasSteps (atState s 5018 (frame f rho)) (atState s 5036 (frame (normalResult s f) rho))
    apply block3Site.lift s _ e (frame f rho)
    simpa only [atState, block3Site.end_pc] using h (UInt256.ofNat 5018)
  · show GasSteps (atState s 5036 (frame f rho)) (atState s 5054 (frame (normalResult s f) rho))
    apply block4Site.lift s _ e (frame f rho)
    simpa only [atState, block4Site.end_pc] using h (UInt256.ofNat 5036)
  · show GasSteps (atState s 5054 (frame f rho)) (atState s 5072 (frame (normalResult s f) rho))
    apply block5Site.lift s _ e (frame f rho)
    simpa only [atState, block5Site.end_pc] using h (UInt256.ofNat 5054)
  · show GasSteps (atState s 5072 (frame f rho)) (atState s 5090 (frame (normalResult s f) rho))
    apply block6Site.lift s _ e (frame f rho)
    simpa only [atState, block6Site.end_pc] using h (UInt256.ofNat 5072)

def movesOf (c : J2FusedSites.Certificates) (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length≤990)
    (hactive : s.activeWords = UInt256.ofNat 1)
    (hinit : GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
      (atState s 4877 (frame (initResult s.executionEnv.calldata.size) rho))) : Moves s rho where
  init := hinit
  first f j hj ht := by
    apply dispatch0Site.lift s _ e (frame f rho)
    simpa only [atState, ht] using
      run_dispatch0 s (UInt256.ofNat 4877) f rho hs e.run (valid_target s e _ _ j hj ht)
  normal j hj f := normalAt s e rho hs hactive j hj f
  tailFinal f hlen hfinal := by
    have g0 : GasSteps (atState s 5090 (frame f rho)) (atState s 5095 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5090) f rho hs e.run
    have g1 : GasSteps (atState s 5095 (pending s f rho)) (atState s 5102 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_pos hfinal] using
        run_finish s (UInt256.ofNat 5095) f rho hs e.run hlen (valid_boundary s e)
    have g2 : GasSteps (atState s 5102 (pending s f rho)) (atState s 5110 (frame (tailResult s f) rho)) := by
      apply finalProjectionSite.lift s _ e (pending s f rho)
      simpa only [atState, finalProjectionSite.end_pc] using
        run_finalProjection s (UInt256.ofNat 5102) f rho hs e.run
    exact g0.trans (g1.trans g2)
  tailBoundary f hlen hfinal _hn256 hmask hshift := by
    have g0 : GasSteps (atState s 5090 (frame f rho)) (atState s 5095 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5090) f rho hs e.run
    have g1 : GasSteps (atState s 5095 (pending s f rho)) (atState s 4891 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_neg hfinal] using
        run_finish s (UInt256.ofNat 5095) f rho hs e.run hlen (valid_boundary s e)
    have g2 := J2FusedSites.longBoundary c s ⟨e.code, e.fork, e.run, e.np⟩
      f rho hs hactive hmask hshift
    exact g0.trans (g1.trans g2)
  fusedBoundary f hlen hfinal h256 := by
    have g0 : GasSteps (atState s 5090 (frame f rho)) (atState s 5095 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5090) f rho hs e.run
    have g1 : GasSteps (atState s 5095 (pending s f rho)) (atState s 4891 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_neg hfinal] using
        run_finish s (UInt256.ofNat 5095) f rho hs e.run hlen (valid_boundary s e)
    have g2 := J2FusedSites.fusedBoundary c s ⟨e.code, e.fork, e.run, e.np⟩
      f rho hs hactive h256 (valid_miss s e)
    exact g0.trans (g1.trans g2)
  transition f hlen := by
    apply transitionSite.lift s _ e (frame f rho)
    simpa only [atState, transitionSite.end_pc] using run_transition s (UInt256.ofNat 4919) f rho hs e.run hlen hactive
  dispatch x f j _hj ht := by
    apply dispatch1Site.lift s _ e (x :: frame f rho)
    have h := run_dispatch1 s (UInt256.ofNat 4955) x f rho hs e.run (valid_block4 s e)
    have he : pcAfter (UInt256.ofNat 4955) dispatch1Template = UInt256.ofNat (blockPC 0) := by decide
    simpa only [atState, he, ← transitionTarget, ht] using h
  result f := by
    apply resultSite.lift s _ e (frame f rho)
    have h := run_result s (UInt256.ofNat 5110) f rho hs e.run (valid_miss s e)
    by_cases hc : f.acc.toNat=0
    · simpa only [atState, resultSite.end_pc, if_pos hc] using h
    · simpa only [atState, resultSite.end_pc, if_neg hc] using h

/-- The scanner's moves; the segment end `clamp size` pushed by the dispatch becomes the frame's `stop` slot. -/
def moves (c : J2FusedSites.Certificates) (s : State) (e : Env s) (rest : List UInt256) (hs : rest.length≤989)
    (hactive : s.activeWords = UInt256.ofNat 1) :
    Moves s rest :=
  movesOf c s e _ (by omega) hactive (by
    apply initSite.lift s _ e _
    simpa only [atState, initSite.end_pc] using run_init s (UInt256.ofNat 4804) rest hs e.run hactive)

#print axioms moves
#print axioms gasSteps_generic_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
