import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144SetupSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144DispatchRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144PadPrefix
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Dispatch
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
def dispatchTemplate : List Instr := Table144DispatchRaw.template 392
theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 311).take dispatchTemplate.length = dispatchTemplate := by rfl
def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchTemplate :=
  StackSiteBuilder.ofSlice dispatchTemplate 311 dispatch_slice
    (by change 311 + dispatchTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchTemplate) (by decide))
    (by decide)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 510 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 311) = UInt256.ofNat 510
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem dispatch_advances : ∀ instruction ∈ dispatchTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

def prefixTemplate : List Instr := Table144PadPrefix.template 32
theorem prefix_slice :
    (Artifact.submissionArtifact.instructions.drop 235).take prefixTemplate.length = prefixTemplate := by rfl
def prefixSite : GenericRoundSite Artifact.submissionArtifact .Osaka prefixTemplate :=
  StackSiteBuilder.ofSlice prefixTemplate 235 prefix_slice
    (by change 235 + prefixTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := prefixTemplate) (by decide))
    (by decide)
theorem prefix_pc : prefixSite.startPC = UInt256.ofNat 392 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 235) = UInt256.ofNat 392
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem prefix_advances : ∀ instruction ∈ prefixTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 392).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 235 = 392 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 235 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 392 = true
  rw [hcode]
  exact h

def gasSteps_miss (s : State) (ptr h0 h1 h2 h3 h4 off : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hmiss : s.executionEnv.calldata.size ≠ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 510, stack := ptr :: h0 :: h1 :: h2 :: h3 :: h4 :: off :: rho}
      {s with pc := UInt256.ofNat 517, stack := ptr :: h0 :: h1 :: h2 :: h3 :: h4 :: off :: rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 510, stack := ptr :: h0 :: h1 :: h2 :: h3 :: h4 :: off :: rho} _ hcode hfork hrun hnp dispatch_pc.symm dispatch_advances
  have h := Table144DispatchRaw.run_miss s (UInt256.ofNat 510) ptr h0 h1 h2 h3 h4 off rho 392 hstack hrun hfit hmiss
  have hp : pcAfter (UInt256.ofNat 510) (Table144DispatchRaw.template 392) = UInt256.ofNat 517 := by rfl
  rw [hp] at h
  exact h

def gasSteps_hit (s : State) (ptr h0 h1 h2 h3 h4 off : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hhit : s.executionEnv.calldata.size = off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 510, stack := ptr :: h0 :: h1 :: h2 :: h3 :: h4 :: off :: rho}
      {s with pc := UInt256.ofNat 392, stack := ptr :: h0 :: h1 :: h2 :: h3 :: h4 :: off :: rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 510, stack := ptr :: h0 :: h1 :: h2 :: h3 :: h4 :: off :: rho} _ hcode hfork hrun hnp dispatch_pc.symm dispatch_advances
  have h := Table144DispatchRaw.run_hit s (UInt256.ofNat 510) ptr h0 h1 h2 h3 h4 off rho 392 hstack hrun hfit hhit (valid_pad s hcode)
  exact h

def gasSteps_prefix (s : State) (ret : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 1019) (hrun : s.halt = .Running)
    (hbound : p + 64 < 2^256) (halign : p % 32 = 0)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 392, stack := UInt256.ofNat p :: ret :: rest}
      {s with pc := UInt256.ofNat 398, stack := ret :: rest, activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p)} := by
  apply PadLift.gasSteps_of_raw prefixSite {s with pc := UInt256.ofNat 392, stack := UInt256.ofNat p :: ret :: rest} _ hcode hfork hrun hnp prefix_pc.symm prefix_advances
  have h := Table144PadPrefix.run_template s (UInt256.ofNat 392) ret p 32 rest hstack hrun hbound halign (by decide)
  have hp : pcAfter (UInt256.ofNat 392) (Table144PadPrefix.template 32) = UInt256.ofNat 398 := by rfl
  rw [hp] at h
  exact h

#print axioms gasSteps_hit
#print axioms gasSteps_miss
#print axioms gasSteps_prefix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Dispatch
