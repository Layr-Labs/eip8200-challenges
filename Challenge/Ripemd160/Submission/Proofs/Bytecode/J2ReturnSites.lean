import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2ReturnSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open J2Sites J2Moves StackRoundTrace StackRoundTemplate
private theorem code_bound : Artifact.submissionArtifact.code.size < 2^256 := by
  change submissionBytecode.size < 2^256
  rw [referenceBytecode_size]
  decide
namespace selector
abbrev template : List Instr := RecognitionSelectorRaw.prefixTemplate (UInt256.ofNat 4939)
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 202).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 202 actual_slice
    (by change 202 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 299 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 202) = UInt256.ofNat 299
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 299) template = UInt256.ofNat 319 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 299 stack) = some t) : GasSteps (atState s 299 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end selector
namespace returned
abbrev template : List Instr := RecognitionSelectorRaw.finish
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 215).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 215 actual_slice
    (by change 215 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 321 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 215) = UInt256.ofNat 321
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem end_pc : pcAfter (UInt256.ofNat 321) template = UInt256.ofNat 323 := by decide
theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 321 stack) = some t) : GasSteps (atState s 321 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm form h
end returned
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2ReturnSites
