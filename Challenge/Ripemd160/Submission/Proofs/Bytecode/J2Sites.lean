import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2HoistSites
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
theorem end_pc : pcAfter (UInt256.ofNat 4804) template = UInt256.ofNat 4874 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4804 stack) = some t) : GasSteps (atState s 4804 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end initSite

namespace dispatch0Site
abbrev template : List Instr := J2Raw.dispatch0Template
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3541).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3541 actual_slice
    (by change 3541 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4874 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3541) = UInt256.ofNat 4874
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4874 stack) = some t) : GasSteps (atState s 4874 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end dispatch0Site

namespace block0Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3595).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3595 actual_slice
    (by change 3595 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4948 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3595) = UInt256.ofNat 4948
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4948) template = UInt256.ofNat 4966 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4948 stack) = some t) : GasSteps (atState s 4948 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block0Site

namespace block1Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3613).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3613 actual_slice
    (by change 3613 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4966 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3613) = UInt256.ofNat 4966
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4966) template = UInt256.ofNat 4984 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4966 stack) = some t) : GasSteps (atState s 4966 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block1Site

namespace block2Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3631).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3631 actual_slice
    (by change 3631 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4984 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3631) = UInt256.ofNat 4984
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4984) template = UInt256.ofNat 5002 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4984 stack) = some t) : GasSteps (atState s 4984 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block2Site

namespace block3Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3649).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3649 actual_slice
    (by change 3649 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5002 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3649) = UInt256.ofNat 5002
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5002) template = UInt256.ofNat 5020 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5002 stack) = some t) : GasSteps (atState s 5002 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block3Site

namespace block4Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3667).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3667 actual_slice
    (by change 3667 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5020 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3667) = UInt256.ofNat 5020
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5020) template = UInt256.ofNat 5038 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5020 stack) = some t) : GasSteps (atState s 5020 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block4Site

namespace block5Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3685).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3685 actual_slice
    (by change 3685 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5038 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3685) = UInt256.ofNat 5038
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5038) template = UInt256.ofNat 5056 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5038 stack) = some t) : GasSteps (atState s 5038 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block5Site

namespace block6Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3703).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3703 actual_slice
    (by change 3703 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5056 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3703) = UInt256.ofNat 5056
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5056) template = UInt256.ofNat 5074 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5056 stack) = some t) : GasSteps (atState s 5056 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block6Site

namespace tailSite
abbrev template : List Instr := J2Raw.tailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3721).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3721 actual_slice
    (by change 3721 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5074 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3721) = UInt256.ofNat 5074
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5074) template = UInt256.ofNat 5079 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5074 stack) = some t) : GasSteps (atState s 5074 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end tailSite

namespace finishSite
abbrev template : List Instr := J2Raw.finishTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3726).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3726 actual_slice
    (by change 3726 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5079 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3726) = UInt256.ofNat 5079
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5079) template = UInt256.ofNat 5086 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5079 stack) = some t) : GasSteps (atState s 5079 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finishSite

namespace finalProjectionSite
abbrev template : List Instr := J2Raw.finalProjectionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3731).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3731 actual_slice
    (by change 3731 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5086 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3731) = UInt256.ofNat 5086
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5086) template = UInt256.ofNat 5096 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5086 stack) = some t) : GasSteps (atState s 5086 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finalProjectionSite

namespace resultSite
abbrev template : List Instr := J2Raw.resultTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3740).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3740 actual_slice
    (by change 3740 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5096 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3740) = UInt256.ofNat 5096
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5096) template = UInt256.ofNat 5100 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5096 stack) = some t) : GasSteps (atState s 5096 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end resultSite

namespace boundaryProjectionSite
abbrev template : List Instr := J2Raw.boundaryProjectionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3565).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3565 actual_slice
    (by change 3565 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4911 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3565) = UInt256.ofNat 4911
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4911) template = UInt256.ofNat 4916 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4911 stack) = some t) : GasSteps (atState s 4911 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end boundaryProjectionSite

theorem valid_block0 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4948 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3595 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3595 = 4948 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block1 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4966 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3613 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3613 = 4966 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block2 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4984 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3631 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3631 = 4984 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block3 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5002 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3649 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3649 = 5002 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block4 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5020 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3667 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3667 = 5020 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block5 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5038 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3685 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3685 = 5038 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block6 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5056 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3703 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3703 = 5056 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block7 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5074 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3721 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3721 = 5074 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_boundary (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4888 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3551 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3551 = 4888 := by
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
  · show GasSteps (atState s 4948 (frame f rho)) (atState s 4966 (frame (normalResult s f) rho))
    apply block0Site.lift s _ e (frame f rho)
    simpa only [atState, block0Site.end_pc] using h (UInt256.ofNat 4948)
  · show GasSteps (atState s 4966 (frame f rho)) (atState s 4984 (frame (normalResult s f) rho))
    apply block1Site.lift s _ e (frame f rho)
    simpa only [atState, block1Site.end_pc] using h (UInt256.ofNat 4966)
  · show GasSteps (atState s 4984 (frame f rho)) (atState s 5002 (frame (normalResult s f) rho))
    apply block2Site.lift s _ e (frame f rho)
    simpa only [atState, block2Site.end_pc] using h (UInt256.ofNat 4984)
  · show GasSteps (atState s 5002 (frame f rho)) (atState s 5020 (frame (normalResult s f) rho))
    apply block3Site.lift s _ e (frame f rho)
    simpa only [atState, block3Site.end_pc] using h (UInt256.ofNat 5002)
  · show GasSteps (atState s 5020 (frame f rho)) (atState s 5038 (frame (normalResult s f) rho))
    apply block4Site.lift s _ e (frame f rho)
    simpa only [atState, block4Site.end_pc] using h (UInt256.ofNat 5020)
  · show GasSteps (atState s 5038 (frame f rho)) (atState s 5056 (frame (normalResult s f) rho))
    apply block5Site.lift s _ e (frame f rho)
    simpa only [atState, block5Site.end_pc] using h (UInt256.ofNat 5038)
  · show GasSteps (atState s 5056 (frame f rho)) (atState s 5074 (frame (normalResult s f) rho))
    apply block6Site.lift s _ e (frame f rho)
    simpa only [atState, block6Site.end_pc] using h (UInt256.ofNat 5056)

def movesOf (c : J2FusedSites.Certificates) (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length≤990)
    (hactive : s.activeWords = UInt256.ofNat 1)
    (hinit : GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
      (atState s 4874 (frame (initResult s.executionEnv.calldata.size) rho))) : Moves s rho where
  init := hinit
  first f j hj ht := by
    apply dispatch0Site.lift s _ e (frame f rho)
    simpa only [atState, ht] using
      run_dispatch0 s (UInt256.ofNat 4874) f rho hs e.run hactive (valid_target s e _ _ j hj ht)
  normal j hj f := normalAt s e rho hs hactive j hj f
  tailFinal f hlen hfinal := by
    have g0 : GasSteps (atState s 5074 (frame f rho)) (atState s 5079 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5074) f rho hs e.run
    have g1 : GasSteps (atState s 5079 (pending s f rho)) (atState s 5086 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_neg (Nat.not_lt_of_ge hfinal)] using
        run_finish s (UInt256.ofNat 5079) f rho hs e.run hlen (valid_boundary s e)
    have g2 : GasSteps (atState s 5086 (pending s f rho)) (atState s 5096 (frame (tailResult s f) rho)) := by
      apply finalProjectionSite.lift s _ e (pending s f rho)
      simpa only [atState, finalProjectionSite.end_pc] using
        run_finalProjection s (UInt256.ofNat 5086) f rho hs e.run hfinal hlen hactive
    exact g0.trans (g1.trans g2)
  tailBoundary f hlen hfinal _hn256 hmask := by
    have g0 : GasSteps (atState s 5074 (frame f rho)) (atState s 5079 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5074) f rho hs e.run
    have g1 : GasSteps (atState s 5079 (pending s f rho)) (atState s 4888 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_pos hfinal] using
        run_finish s (UInt256.ofNat 5079) f rho hs e.run hlen (valid_boundary s e)
    have g2 := J2FusedSites.longBoundary c s ⟨e.code, e.fork, e.run, e.np⟩
      f rho hs hactive hmask hfinal
    exact g0.trans (g1.trans g2)
  fusedBoundary f hlen hfinal h256 := by
    have g0 : GasSteps (atState s 5074 (frame f rho)) (atState s 5079 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5074) f rho hs e.run
    have g1 : GasSteps (atState s 5079 (pending s f rho)) (atState s 4888 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_pos hfinal] using
        run_finish s (UInt256.ofNat 5079) f rho hs e.run hlen (valid_boundary s e)
    have g2 := J2FusedSites.fusedBoundary c s ⟨e.code, e.fork, e.run, e.np⟩
      f rho hs hactive h256 (valid_miss s e)
    exact g0.trans (g1.trans g2)
  transition f hlen := by
    exact J2HoistSites.gasSteps s ⟨e.code, e.fork, e.run, e.np⟩ f rho hs hactive hlen
      (valid_block4 s e)
  result f := by
    apply resultSite.lift s _ e (frame f rho)
    have h := run_result s (UInt256.ofNat 5096) f rho hs e.run (valid_miss s e)
    by_cases hc : f.acc.toNat=0
    · simpa only [atState, resultSite.end_pc, if_pos hc] using h
    · simpa only [atState, resultSite.end_pc, if_neg hc] using h

/-- The scanner's moves; the segment end `clamp size` pushed by the dispatch becomes the frame's `stop` slot. -/
def moves (c : J2FusedSites.Certificates) (s : State) (e : Env s) (rest : List UInt256) (hs : rest.length≤989)
    (hactive : s.activeWords = UInt256.ofNat 1) :
    Moves s rest :=
  movesOf c s e _ (by omega) hactive (by
    apply initSite.lift s _ e _
    simpa only [atState, initSite.end_pc] using run_init s (UInt256.ofNat 4804) rest (by omega) e.run)

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

#print axioms moves
#print axioms gasSteps_generic_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
