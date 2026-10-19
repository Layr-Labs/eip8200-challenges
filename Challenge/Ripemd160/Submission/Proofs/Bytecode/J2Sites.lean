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
theorem end_pc : pcAfter (UInt256.ofNat 4804) template = UInt256.ofNat 4839 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4804 stack) = some t) : GasSteps (atState s 4804 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end initSite

namespace dispatch0Site
abbrev template : List Instr := J2Raw.dispatch0Template
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3538).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3538 actual_slice
    (by change 3538 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4839 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3538) = UInt256.ofNat 4839
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4839 stack) = some t) : GasSteps (atState s 4839 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end dispatch0Site

namespace block0Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3587).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3587 actual_slice
    (by change 3587 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4970 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3587) = UInt256.ofNat 4970
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4970) template = UInt256.ofNat 5052 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4970 stack) = some t) : GasSteps (atState s 4970 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block0Site

namespace block1Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3605).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3605 actual_slice
    (by change 3605 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5052 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3605) = UInt256.ofNat 5052
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5052) template = UInt256.ofNat 5134 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5052 stack) = some t) : GasSteps (atState s 5052 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block1Site

namespace block2Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3623).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3623 actual_slice
    (by change 3623 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5134 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3623) = UInt256.ofNat 5134
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5134) template = UInt256.ofNat 5216 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5134 stack) = some t) : GasSteps (atState s 5134 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block2Site

namespace block3Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3641).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3641 actual_slice
    (by change 3641 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5216 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3641) = UInt256.ofNat 5216
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5216) template = UInt256.ofNat 5298 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5216 stack) = some t) : GasSteps (atState s 5216 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block3Site

namespace block4Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3659).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3659 actual_slice
    (by change 3659 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5298 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3659) = UInt256.ofNat 5298
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5298) template = UInt256.ofNat 5380 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5298 stack) = some t) : GasSteps (atState s 5298 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block4Site

namespace block5Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3677).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3677 actual_slice
    (by change 3677 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5380 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3677) = UInt256.ofNat 5380
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5380) template = UInt256.ofNat 5462 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5380 stack) = some t) : GasSteps (atState s 5380 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block5Site

namespace block6Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3695).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3695 actual_slice
    (by change 3695 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5462 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3695) = UInt256.ofNat 5462
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5462) template = UInt256.ofNat 5544 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5462 stack) = some t) : GasSteps (atState s 5462 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block6Site

namespace tailSite
abbrev template : List Instr := J2Raw.tailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3713).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3713 actual_slice
    (by change 3713 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5544 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3713) = UInt256.ofNat 5544
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5544) template = UInt256.ofNat 5549 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5544 stack) = some t) : GasSteps (atState s 5544 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end tailSite

namespace finishSite
abbrev template : List Instr := J2Raw.finishTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3718).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3718 actual_slice
    (by change 3718 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5549 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3718) = UInt256.ofNat 5549
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5549) template = UInt256.ofNat 5556 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5549 stack) = some t) : GasSteps (atState s 5549 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finishSite

namespace finalProjectionSite
abbrev template : List Instr := J2Raw.finalProjectionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3723).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3723 actual_slice
    (by change 3723 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5556 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3723) = UInt256.ofNat 5556
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5556) template = UInt256.ofNat 5566 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5556 stack) = some t) : GasSteps (atState s 5556 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finalProjectionSite

namespace resultSite
abbrev template : List Instr := J2Raw.resultTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3732).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3732 actual_slice
    (by change 3732 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5566 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3732) = UInt256.ofNat 5566
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5566) template = UInt256.ofNat 5570 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5566 stack) = some t) : GasSteps (atState s 5566 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end resultSite

namespace boundaryProjectionSite
abbrev template : List Instr := J2Raw.boundaryProjectionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3562).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3562 actual_slice
    (by change 3562 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4876 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3562) = UInt256.ofNat 4876
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4876) template = UInt256.ofNat 4881 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4876 stack) = some t) : GasSteps (atState s 4876 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end boundaryProjectionSite

theorem valid_block0 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4970 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3587 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3587 = 4968 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block1 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5052 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3605 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3605 = 4986 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block2 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5134 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3623 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3623 = 5004 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block3 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5216 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3641 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3641 = 5022 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block4 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5298 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3659 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3659 = 5040 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block5 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5380 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3677 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3677 = 5058 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block6 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5462 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3695 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3695 = 5076 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block7 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5544 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3713 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3713 = 5094 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_boundary (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4853 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3548 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3548 = 4929 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_miss (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4565 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3412 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3412 = 4617 := by
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
  · show GasSteps (atState s 4970 (frame f rho)) (atState s 5052 (frame (normalResult s f) rho))
    apply block0Site.lift s _ e (frame f rho)
    simpa only [atState, block0Site.end_pc] using h (UInt256.ofNat 4970)
  · show GasSteps (atState s 5052 (frame f rho)) (atState s 5134 (frame (normalResult s f) rho))
    apply block1Site.lift s _ e (frame f rho)
    simpa only [atState, block1Site.end_pc] using h (UInt256.ofNat 5052)
  · show GasSteps (atState s 5134 (frame f rho)) (atState s 5216 (frame (normalResult s f) rho))
    apply block2Site.lift s _ e (frame f rho)
    simpa only [atState, block2Site.end_pc] using h (UInt256.ofNat 5134)
  · show GasSteps (atState s 5216 (frame f rho)) (atState s 5298 (frame (normalResult s f) rho))
    apply block3Site.lift s _ e (frame f rho)
    simpa only [atState, block3Site.end_pc] using h (UInt256.ofNat 5216)
  · show GasSteps (atState s 5298 (frame f rho)) (atState s 5380 (frame (normalResult s f) rho))
    apply block4Site.lift s _ e (frame f rho)
    simpa only [atState, block4Site.end_pc] using h (UInt256.ofNat 5298)
  · show GasSteps (atState s 5380 (frame f rho)) (atState s 5462 (frame (normalResult s f) rho))
    apply block5Site.lift s _ e (frame f rho)
    simpa only [atState, block5Site.end_pc] using h (UInt256.ofNat 5380)
  · show GasSteps (atState s 5462 (frame f rho)) (atState s 5544 (frame (normalResult s f) rho))
    apply block6Site.lift s _ e (frame f rho)
    simpa only [atState, block6Site.end_pc] using h (UInt256.ofNat 5462)

def movesOf (c : J2FusedSites.Certificates) (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length≤990)
    (hactive : s.activeWords = UInt256.ofNat 1)
    (hinit : GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
      (atState s 4839 (frame (initResult s.executionEnv.calldata.size) rho))) : Moves s rho where
  init := hinit
  first f j hj ht := by
    apply dispatch0Site.lift s _ e (frame f rho)
    simpa only [atState, ht] using
      run_dispatch0 s (UInt256.ofNat 4839) f rho hs e.run hactive (valid_target s e _ _ j hj ht)
  normal j hj f := normalAt s e rho hs hactive j hj f
  tailFinal f hlen hfinal := by
    have g0 : GasSteps (atState s 5544 (frame f rho)) (atState s 5549 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5544) f rho hs e.run
    have g1 : GasSteps (atState s 5549 (pending s f rho)) (atState s 5556 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_neg (Nat.not_lt_of_ge hfinal)] using
        run_finish s (UInt256.ofNat 5549) f rho hs e.run hlen (valid_boundary s e)
    have g2 : GasSteps (atState s 5556 (pending s f rho)) (atState s 5566 (frame (tailResult s f) rho)) := by
      apply finalProjectionSite.lift s _ e (pending s f rho)
      simpa only [atState, finalProjectionSite.end_pc] using
        run_finalProjection s (UInt256.ofNat 5556) f rho hs e.run hfinal hlen hactive
    exact g0.trans (g1.trans g2)
  tailBoundary f hlen hfinal _hn256 hmask := by
    have g0 : GasSteps (atState s 5544 (frame f rho)) (atState s 5549 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5544) f rho hs e.run
    have g1 : GasSteps (atState s 5549 (pending s f rho)) (atState s 4853 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_pos hfinal] using
        run_finish s (UInt256.ofNat 5549) f rho hs e.run hlen (valid_boundary s e)
    have g2 := J2FusedSites.longBoundary c s ⟨e.code, e.fork, e.run, e.np⟩
      f rho hs hactive hmask hfinal
    exact g0.trans (g1.trans g2)
  fusedBoundary f hlen hfinal h256 := by
    have g0 : GasSteps (atState s 5544 (frame f rho)) (atState s 5549 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5544) f rho hs e.run
    have g1 : GasSteps (atState s 5549 (pending s f rho)) (atState s 4853 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_pos hfinal] using
        run_finish s (UInt256.ofNat 5549) f rho hs e.run hlen (valid_boundary s e)
    have g2 := J2FusedSites.fusedBoundary c s ⟨e.code, e.fork, e.run, e.np⟩
      f rho hs hactive h256 (valid_miss s e)
    exact g0.trans (g1.trans g2)
  transition f hlen := by
    exact J2HoistSites.gasSteps s ⟨e.code, e.fork, e.run, e.np⟩ f rho hs hactive hlen
      (valid_block4 s e)
  result f := by
    apply resultSite.lift s _ e (frame f rho)
    have h := run_result s (UInt256.ofNat 5566) f rho hs e.run (valid_miss s e)
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
