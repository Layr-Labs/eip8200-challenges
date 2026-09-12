import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SetupSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadDispatch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefix
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Dispatch
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
def dispatchTemplate : List Instr := PadDispatch.template 408
theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 325).take dispatchTemplate.length = dispatchTemplate := by rfl
def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchTemplate :=
  StackSiteBuilder.ofSlice dispatchTemplate 325 dispatch_slice
    (by change 325 + dispatchTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchTemplate) (by decide))
    (by decide)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 532 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 325) = UInt256.ofNat 532
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem dispatch_advances : ∀ instruction ∈ dispatchTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

def prefixTemplate : List Instr := PadPrefix.dropTemplate
theorem prefix_slice :
    (Artifact.submissionArtifact.instructions.drop 248).take prefixTemplate.length = prefixTemplate := by rfl
def prefixSite : GenericRoundSite Artifact.submissionArtifact .Osaka prefixTemplate :=
  StackSiteBuilder.ofSlice prefixTemplate 248 prefix_slice
    (by change 248 + prefixTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := prefixTemplate) (by decide))
    (by decide)
theorem prefix_pc : prefixSite.startPC = UInt256.ofNat 408 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 248) = UInt256.ofNat 408
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem prefix_advances : ∀ instruction ∈ prefixTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 408).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 248 = 408 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 248 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 408 = true
  rw [hcode]
  exact h

def gasSteps_miss (s : State) (ptr ret off : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1017) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hmiss : s.executionEnv.calldata.size ≠ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 532, stack := ptr :: ret :: off :: rho}
      {s with pc := UInt256.ofNat 539, stack := ptr :: ret :: off :: rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 532, stack := ptr :: ret :: off :: rho} _ hcode hfork hrun hnp dispatch_pc.symm dispatch_advances
  have h := PadDispatch.run_miss s (UInt256.ofNat 532) ptr ret off rho 408 hstack hrun hfit hmiss
  have hp : pcAfter (UInt256.ofNat 532) (PadDispatch.template 408) = UInt256.ofNat 539 := by rfl
  rw [hp] at h
  exact h

def gasSteps_hit (s : State) (ptr ret off : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1017) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hhit : s.executionEnv.calldata.size = off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 532, stack := ptr :: ret :: off :: rho}
      {s with pc := UInt256.ofNat 408, stack := ptr :: ret :: off :: rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 532, stack := ptr :: ret :: off :: rho} _ hcode hfork hrun hnp dispatch_pc.symm dispatch_advances
  have h := PadDispatch.run_hit s (UInt256.ofNat 532) ptr ret off rho 408 hstack hrun hfit hhit (valid_pad s hcode)
  exact h

def gasSteps_prefix (s : State) (ret : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 1019) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 408, stack := UInt256.ofNat p :: ret :: rest}
      {s with pc := UInt256.ofNat 410, stack := ret :: rest} := by
  apply PadLift.gasSteps_of_raw prefixSite {s with pc := UInt256.ofNat 408, stack := UInt256.ofNat p :: ret :: rest} _ hcode hfork hrun hnp prefix_pc.symm prefix_advances
  have h := PadPrefix.run_drop s (UInt256.ofNat 408) ret p rest hstack hrun
  have hp : pcAfter (UInt256.ofNat 408) (PadPrefix.dropTemplate) = UInt256.ofNat 410 := by rfl
  rw [hp] at h
  exact h

#print axioms gasSteps_hit
#print axioms gasSteps_miss
#print axioms gasSteps_prefix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Dispatch
