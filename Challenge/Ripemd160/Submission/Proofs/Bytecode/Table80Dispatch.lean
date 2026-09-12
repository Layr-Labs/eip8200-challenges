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
def dispatchTemplate : List Instr := PadDispatch.template1 404
theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 313).take dispatchTemplate.length = dispatchTemplate := by rfl
def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchTemplate :=
  StackSiteBuilder.ofSlice dispatchTemplate 313 dispatch_slice
    (by change 313 + dispatchTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchTemplate) (by decide))
    (by decide)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 516 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 313) = UInt256.ofNat 516
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem dispatch_advances : ∀ instruction ∈ dispatchTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

def prefixTemplate : List Instr := PadPrefix.dropTemplate
theorem prefix_slice :
    (Artifact.submissionArtifact.instructions.drop 246).take prefixTemplate.length = prefixTemplate := by rfl
def prefixSite : GenericRoundSite Artifact.submissionArtifact .Osaka prefixTemplate :=
  StackSiteBuilder.ofSlice prefixTemplate 246 prefix_slice
    (by change 246 + prefixTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := prefixTemplate) (by decide))
    (by decide)
theorem prefix_pc : prefixSite.startPC = UInt256.ofNat 404 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 246) = UInt256.ofNat 404
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem prefix_advances : ∀ instruction ∈ prefixTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 404).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 246 = 404 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 246 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 404 = true
  rw [hcode]
  exact h

def gasSteps_miss (s : State) (ptr off : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1018) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hmiss : s.executionEnv.calldata.size ≠ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 516, stack := ptr :: off :: rho}
      {s with pc := UInt256.ofNat 523, stack := ptr :: off :: rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 516, stack := ptr :: off :: rho} _ hcode hfork hrun hnp dispatch_pc.symm dispatch_advances
  have h := PadDispatch.run_miss1 s (UInt256.ofNat 516) ptr off rho 404 hstack hrun hfit hmiss
  have hp : pcAfter (UInt256.ofNat 516) (PadDispatch.template1 404) = UInt256.ofNat 523 := by rfl
  rw [hp] at h
  exact h

def gasSteps_hit (s : State) (ptr off : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1018) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hhit : s.executionEnv.calldata.size = off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 516, stack := ptr :: off :: rho}
      {s with pc := UInt256.ofNat 404, stack := ptr :: off :: rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 516, stack := ptr :: off :: rho} _ hcode hfork hrun hnp dispatch_pc.symm dispatch_advances
  have h := PadDispatch.run_hit1 s (UInt256.ofNat 516) ptr off rho 404 hstack hrun hfit hhit (valid_pad s hcode)
  exact h

def gasSteps_prefix (s : State) (ret : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 1019) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 404, stack := UInt256.ofNat p :: ret :: rest}
      {s with pc := UInt256.ofNat 406, stack := ret :: rest} := by
  apply PadLift.gasSteps_of_raw prefixSite {s with pc := UInt256.ofNat 404, stack := UInt256.ofNat p :: ret :: rest} _ hcode hfork hrun hnp prefix_pc.symm prefix_advances
  have h := PadPrefix.run_drop s (UInt256.ofNat 404) ret p rest hstack hrun
  have hp : pcAfter (UInt256.ofNat 404) (PadPrefix.dropTemplate) = UInt256.ofNat 406 := by rfl
  rw [hp] at h
  exact h

#print axioms gasSteps_hit
#print axioms gasSteps_miss
#print axioms gasSteps_prefix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Dispatch
