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
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3598).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3598 actual_slice
    (by change 3598 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4951 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3598) = UInt256.ofNat 4951
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4951) template = UInt256.ofNat 4969 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4951 stack) = some t) : GasSteps (atState s 4951 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block0Site

namespace block1Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3616).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3616 actual_slice
    (by change 3616 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4969 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3616) = UInt256.ofNat 4969
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4969) template = UInt256.ofNat 4987 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4969 stack) = some t) : GasSteps (atState s 4969 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block1Site

namespace block2Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3634).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3634 actual_slice
    (by change 3634 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4987 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3634) = UInt256.ofNat 4987
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 4987) template = UInt256.ofNat 5005 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4987 stack) = some t) : GasSteps (atState s 4987 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block2Site

namespace block3Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3652).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3652 actual_slice
    (by change 3652 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5005 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3652) = UInt256.ofNat 5005
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5005) template = UInt256.ofNat 5023 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5005 stack) = some t) : GasSteps (atState s 5005 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block3Site

namespace block4Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3670).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3670 actual_slice
    (by change 3670 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5023 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3670) = UInt256.ofNat 5023
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5023) template = UInt256.ofNat 5041 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5023 stack) = some t) : GasSteps (atState s 5023 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block4Site

namespace block5Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3688).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3688 actual_slice
    (by change 3688 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5041 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3688) = UInt256.ofNat 5041
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5041) template = UInt256.ofNat 5059 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5041 stack) = some t) : GasSteps (atState s 5041 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block5Site

namespace block6Site
abbrev template : List Instr := J2Raw.normalTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3706).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3706 actual_slice
    (by change 3706 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5059 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3706) = UInt256.ofNat 5059
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5059) template = UInt256.ofNat 5077 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5059 stack) = some t) : GasSteps (atState s 5059 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end block6Site

namespace tailSite
abbrev template : List Instr := J2Raw.tailTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3724).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3724 actual_slice
    (by change 3724 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5077 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3724) = UInt256.ofNat 5077
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5077) template = UInt256.ofNat 5082 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5077 stack) = some t) : GasSteps (atState s 5077 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end tailSite

namespace finishSite
abbrev template : List Instr := J2Raw.finishTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3729).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3729 actual_slice
    (by change 3729 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5082 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3729) = UInt256.ofNat 5082
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5082) template = UInt256.ofNat 5089 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5082 stack) = some t) : GasSteps (atState s 5082 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finishSite

namespace finalProjectionSite
abbrev template : List Instr := J2Raw.finalProjectionTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3734).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3734 actual_slice
    (by change 3734 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5089 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3734) = UInt256.ofNat 5089
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5089) template = UInt256.ofNat 5097 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5089 stack) = some t) : GasSteps (atState s 5089 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end finalProjectionSite

namespace resultSite
abbrev template : List Instr := J2Raw.resultTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3741).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3741 actual_slice
    (by change 3741 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5097 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3741) = UInt256.ofNat 5097
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 5097) template = UInt256.ofNat 5101 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5097 stack) = some t) : GasSteps (atState s 5097 stack) t :=
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

theorem valid_block0 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4951 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3598 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3598 = 4951 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block1 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4969 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3616 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3616 = 4969 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block2 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 4987 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3634 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3634 = 4987 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block3 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5005 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3652 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3652 = 5005 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block4 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5023 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3670 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3670 = 5023 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block5 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5041 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3688 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3688 = 5041 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block6 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5059 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3706 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3706 = 5059 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

theorem valid_block7 (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5077 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3724 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3724 = 5077 := by
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
  · show GasSteps (atState s 4951 (frame f rho)) (atState s 4969 (frame (normalResult s f) rho))
    apply block0Site.lift s _ e (frame f rho)
    simpa only [atState, block0Site.end_pc] using h (UInt256.ofNat 4951)
  · show GasSteps (atState s 4969 (frame f rho)) (atState s 4987 (frame (normalResult s f) rho))
    apply block1Site.lift s _ e (frame f rho)
    simpa only [atState, block1Site.end_pc] using h (UInt256.ofNat 4969)
  · show GasSteps (atState s 4987 (frame f rho)) (atState s 5005 (frame (normalResult s f) rho))
    apply block2Site.lift s _ e (frame f rho)
    simpa only [atState, block2Site.end_pc] using h (UInt256.ofNat 4987)
  · show GasSteps (atState s 5005 (frame f rho)) (atState s 5023 (frame (normalResult s f) rho))
    apply block3Site.lift s _ e (frame f rho)
    simpa only [atState, block3Site.end_pc] using h (UInt256.ofNat 5005)
  · show GasSteps (atState s 5023 (frame f rho)) (atState s 5041 (frame (normalResult s f) rho))
    apply block4Site.lift s _ e (frame f rho)
    simpa only [atState, block4Site.end_pc] using h (UInt256.ofNat 5023)
  · show GasSteps (atState s 5041 (frame f rho)) (atState s 5059 (frame (normalResult s f) rho))
    apply block5Site.lift s _ e (frame f rho)
    simpa only [atState, block5Site.end_pc] using h (UInt256.ofNat 5041)
  · show GasSteps (atState s 5059 (frame f rho)) (atState s 5077 (frame (normalResult s f) rho))
    apply block6Site.lift s _ e (frame f rho)
    simpa only [atState, block6Site.end_pc] using h (UInt256.ofNat 5059)

def movesOf (c : J2FusedSites.Certificates) (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length≤990)
    (hactive : s.activeWords = UInt256.ofNat 1)
    (hinit : GasSteps (atState s 4804 (clamp (UInt256.ofNat s.executionEnv.calldata.size) :: rho))
      (atState s 4877 (frame (initResult s.executionEnv.calldata.size) rho))) : Moves s rho where
  init := hinit
  first f j hj ht := by
    apply dispatch0Site.lift s _ e (frame f rho)
    simpa only [atState, ht] using
      run_dispatch0 s (UInt256.ofNat 4877) f rho hs e.run hactive (valid_target s e _ _ j hj ht)
  normal j hj f := normalAt s e rho hs hactive j hj f
  tailFinal f hlen hfinal := by
    have g0 : GasSteps (atState s 5077 (frame f rho)) (atState s 5082 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5077) f rho hs e.run
    have g1 : GasSteps (atState s 5082 (pending s f rho)) (atState s 5089 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_neg (Nat.not_lt_of_ge hfinal)] using
        run_finish s (UInt256.ofNat 5082) f rho hs e.run hlen (valid_boundary s e)
    have g2 : GasSteps (atState s 5089 (pending s f rho)) (atState s 5097 (frame (tailResult s f) rho)) := by
      apply finalProjectionSite.lift s _ e (pending s f rho)
      simpa only [atState, finalProjectionSite.end_pc] using
        run_finalProjection s (UInt256.ofNat 5089) f rho hs e.run hfinal
    exact g0.trans (g1.trans g2)
  tailBoundary f hlen hfinal _hn256 hmask := by
    have g0 : GasSteps (atState s 5077 (frame f rho)) (atState s 5082 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5077) f rho hs e.run
    have g1 : GasSteps (atState s 5082 (pending s f rho)) (atState s 4891 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_pos hfinal] using
        run_finish s (UInt256.ofNat 5082) f rho hs e.run hlen (valid_boundary s e)
    have g2 := J2FusedSites.longBoundary c s ⟨e.code, e.fork, e.run, e.np⟩
      f rho hs hactive hmask hfinal
    exact g0.trans (g1.trans g2)
  fusedBoundary f hlen hfinal h256 := by
    have g0 : GasSteps (atState s 5077 (frame f rho)) (atState s 5082 (pending s f rho)) := by
      apply tailSite.lift s _ e (frame f rho)
      simpa only [atState, tailSite.end_pc] using run_tail s (UInt256.ofNat 5077) f rho hs e.run
    have g1 : GasSteps (atState s 5082 (pending s f rho)) (atState s 4891 (pending s f rho)) := by
      apply finishSite.lift s _ e (pending s f rho)
      simpa only [atState, finishSite.end_pc, if_pos hfinal] using
        run_finish s (UInt256.ofNat 5082) f rho hs e.run hlen (valid_boundary s e)
    have g2 := J2FusedSites.fusedBoundary c s ⟨e.code, e.fork, e.run, e.np⟩
      f rho hs hactive h256 (valid_miss s e)
    exact g0.trans (g1.trans g2)
  transition f hlen := by
    exact J2HoistSites.gasSteps s ⟨e.code, e.fork, e.run, e.np⟩ f rho hs hactive hlen
      (valid_block4 s e)
  result f := by
    apply resultSite.lift s _ e (frame f rho)
    have h := run_result s (UInt256.ofNat 5097) f rho hs e.run (valid_miss s e)
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
