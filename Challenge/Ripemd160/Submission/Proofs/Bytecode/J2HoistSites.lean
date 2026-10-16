import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2HoistRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedSites

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2HoistSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate J2Raw J2Moves J2HoistRaw
open J2FusedSites (Env)

private theorem code_bound : Artifact.submissionArtifact.code.size < 2^256 := by
  change submissionBytecode.size < 2^256
  rw [referenceBytecode_size]
  decide

namespace prefixSite
abbrev template : List Instr := prefixTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3572).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3572 actual_slice
    (by change 3572 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4919 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3572) = UInt256.ofNat 4919
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4919 stack) = some t) : GasSteps (atState s 4919 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm
    (RecognitionLift.advancesAll_sound _ (by decide)) h
end prefixSite

namespace branchSite
abbrev template : List Instr := J2HoistRaw.branchTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3587).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3587 actual_slice
    (by change 3587 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4936 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3587) = UInt256.ofNat 4936
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4936 stack) = some t) : GasSteps (atState s 4936 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm
    (RecognitionLift.advancesAll_sound _ (by decide)) h
end branchSite

namespace genericSite
abbrev template : List Instr := genericTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3592).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3592 actual_slice
    (by change 3592 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4944 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3592) = UInt256.ofNat 4944
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 4944 stack) = some t) : GasSteps (atState s 4944 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm
    (RecognitionLift.advancesAll_sound _ (by decide)) h
end genericSite

namespace specialSite
abbrev template : List Instr := specialTemplate
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 3751).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3751 actual_slice
    (by change 3751 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 5109 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3751) = UInt256.ofNat 5109
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
def lift (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq template (atState s 5109 stack) = some t) : GasSteps (atState s 5109 stack) t :=
  RecognitionLift.gasSteps_of_raw site _ _ e.code e.fork e.run e.np site_pc.symm
    (RecognitionLift.advancesAll_sound _ (by decide)) h
end specialSite

theorem valid_special (s : State) (e : Env s) : Decode.isValidJumpDest s.executionEnv.code 5109 = true := by
  rw [e.code]
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3751 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3751 = 5109 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  simpa only [hp] using h

def gasSteps (s : State) (e : Env s) (f : J2Raw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hactive : s.activeWords = UInt256.ofNat 1)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (blockPC 4) = true) :
    GasSteps (atState s 4919 (frame f rho))
      (atState s (transitionTarget (UInt256.ofNat s.executionEnv.calldata.size)).toNat
        (frame (transitionResult f) rho)) := by
  have hp : GasSteps (atState s 4919 (frame f rho)) (atState s 4936 (frame (mid f) rho)) := by
    apply prefixSite.lift s _ e _
    simpa only [atState, show pcAfter (UInt256.ofNat 4919) prefixTemplate = UInt256.ofNat 4936 from by decide]
      using run_prefix s (UInt256.ofNat 4919) f rho hs e.run
  have hb := run_branch s (UInt256.ofNat 4936) (frame (mid f) rho)
    (by simp [frame]; omega) e.run (valid_special s e)
  have gb := branchSite.lift s _ e _ hb
  by_cases hc : UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) (UInt256.ofNat 16) = 0
  · have gb' : GasSteps (atState s 4936 (frame (mid f) rho)) (atState s 4944 (frame (mid f) rho)) := by
      simpa only [atState, hc, if_true,
        show pcAfter (UInt256.ofNat 4936) J2HoistRaw.branchTemplate = UInt256.ofNat 4944 from by decide] using gb
    have hg : GasSteps (atState s 4944 (frame (mid f) rho))
        (atState s 4956 (frame (transitionResult f) rho)) := by
      apply genericSite.lift s _ e _
      simpa only [atState, mid, post, transitionResult, transitionStop, hlen, hc, if_true,
        show pcAfter (UInt256.ofNat 4944) genericTemplate = UInt256.ofNat 4956 from by decide]
        using run_generic s (UInt256.ofNat 4944) (mid f) rho hs e.run hlen hactive
    simpa only [transitionTarget, hc, if_true, show (UInt256.ofNat (blockPC 0)).toNat = 4956 from by decide]
      using hp.trans (gb'.trans hg)
  · have gb' : GasSteps (atState s 4936 (frame (mid f) rho)) (atState s 5109 (frame (mid f) rho)) := by
      simpa only [atState, hc, if_false] using gb
    have hg : GasSteps (atState s 5109 (frame (mid f) rho))
        (atState s (blockPC 4) (frame (transitionResult f) rho)) := by
      apply specialSite.lift s _ e _
      have h := run_special s (UInt256.ofNat 5109) (mid f) rho hs e.run hlen hactive hvalid
      simpa only [atState, mid, post, transitionResult, transitionStop, hlen, hc, if_false] using h
    simpa only [transitionTarget, hc, if_false,
      show (UInt256.ofNat (blockPC 4)).toNat = blockPC 4 from by decide] using hp.trans (gb'.trans hg)

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2HoistSites
