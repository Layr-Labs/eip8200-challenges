import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineBoundarySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadDispatch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlySchedule
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace

def dispatchTemplate : List Instr := PadDispatch.template 396
theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 287).take dispatchTemplate.length = dispatchTemplate := by rfl
def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchTemplate :=
  StackSiteBuilder.ofSlice dispatchTemplate 287 dispatch_slice
    (by change 287 + dispatchTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchTemplate) (by decide))
    (by decide)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 471 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 287) = UInt256.ofNat 471
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem dispatch_advances : ∀ instruction ∈ dispatchTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

def prefixTemplate : List Instr := PadPrefix.template 32
theorem prefix_slice :
    (Artifact.submissionArtifact.instructions.drop 240).take prefixTemplate.length = prefixTemplate := by rfl
def prefixSite : GenericRoundSite Artifact.submissionArtifact .Osaka prefixTemplate :=
  StackSiteBuilder.ofSlice prefixTemplate 240 prefix_slice
    (by change 240 + prefixTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := prefixTemplate) (by decide))
    (by decide)
theorem prefix_pc : prefixSite.startPC = UInt256.ofNat 396 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 240) = UInt256.ofNat 396
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem prefix_advances : ∀ instruction ∈ prefixTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

def bodyTemplate : List Instr := PadOnlySchedule.template
theorem body_slice :
    (Artifact.submissionArtifact.instructions.drop 245).take bodyTemplate.length = bodyTemplate := by rfl
def bodySite : GenericRoundSite Artifact.submissionArtifact .Osaka bodyTemplate :=
  StackSiteBuilder.ofSlice bodyTemplate 245 body_slice
    (by change 245 + bodyTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := bodyTemplate) (by decide))
    (by decide)
theorem body_pc : bodySite.startPC = UInt256.ofNat 402 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 245) = UInt256.ofNat 402
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem body_advances : ∀ instruction ∈ bodyTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

def jumpTemplate : List Instr := PadJump.template 712
theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 272).take jumpTemplate.length = jumpTemplate := by rfl
def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpTemplate :=
  StackSiteBuilder.ofSlice jumpTemplate 272 jump_slice
    (by change 272 + jumpTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := jumpTemplate) (by decide))
    (by decide)
theorem jump_pc : jumpSite.startPC = UInt256.ofNat 447 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 272) = UInt256.ofNat 447
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem jump_advances : ∀ instruction ∈ jumpTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

def mergeTemplate : List Instr := [.op .JUMPDEST]
theorem merge_slice :
    (Artifact.submissionArtifact.instructions.drop 464).take mergeTemplate.length = mergeTemplate := by rfl
def mergeSite : GenericRoundSite Artifact.submissionArtifact .Osaka mergeTemplate :=
  StackSiteBuilder.ofSlice mergeTemplate 464 merge_slice
    (by change 464 + mergeTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := mergeTemplate) (by decide))
    (by decide)
theorem merge_pc : mergeSite.startPC = UInt256.ofNat 712 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 464) = UInt256.ofNat 712
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem merge_advances : ∀ instruction ∈ mergeTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 396).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 240 = 396 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 240 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 396 = true
  rw [hcode]
  exact h

theorem valid_merge (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 712).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 464 = 712 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 464 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 712 = true
  rw [hcode]
  exact h

def gasSteps_miss (s : State) (ptr ret off : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1017) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hmiss : s.executionEnv.calldata.size ≠ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 471, stack := ptr :: ret :: off :: rho}
      {s with pc := UInt256.ofNat 478, stack := ptr :: ret :: off :: rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 471, stack := ptr :: ret :: off :: rho} _ hcode hfork hrun hnp dispatch_pc.symm dispatch_advances
  have h := PadDispatch.run_miss s (UInt256.ofNat 471) ptr ret off rho 396 hstack hrun hfit hmiss
  have hp : pcAfter (UInt256.ofNat 471) (PadDispatch.template 396) = UInt256.ofNat 478 := by rfl
  rw [hp] at h
  exact h

def gasSteps_hit (s : State) (ptr ret off : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1017) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hhit : s.executionEnv.calldata.size = off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 471, stack := ptr :: ret :: off :: rho}
      {s with pc := UInt256.ofNat 396, stack := ptr :: ret :: off :: rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 471, stack := ptr :: ret :: off :: rho} _ hcode hfork hrun hnp dispatch_pc.symm dispatch_advances
  have h := PadDispatch.run_hit s (UInt256.ofNat 471) ptr ret off rho 396 hstack hrun hfit hhit (valid_pad s hcode)
  exact h

def gasSteps_prefix (s : State) (ret : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 1019) (hrun : s.halt = .Running)
    (hbound : p + 64 < 2^256) (halign : p % 32 = 0)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 396, stack := UInt256.ofNat p :: ret :: rest}
      {s with pc := UInt256.ofNat 402, stack := ret :: rest, activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p)} := by
  apply PadLift.gasSteps_of_raw prefixSite {s with pc := UInt256.ofNat 396, stack := UInt256.ofNat p :: ret :: rest} _ hcode hfork hrun hnp prefix_pc.symm prefix_advances
  have h := PadPrefix.run_template s (UInt256.ofNat 396) ret p 32 rest hstack hrun hbound halign (by decide)
  have hp : pcAfter (UInt256.ofNat 396) (PadPrefix.template 32) = UInt256.ofNat 402 := by rfl
  rw [hp] at h
  exact h

def gasSteps_body (s : State) (ret : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 402, stack := ret :: rest}
      {s with pc := UInt256.ofNat 447, stack := [UInt256.ofNat 22, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0] ++ (ret :: rest), memory := PadOnlySchedule.resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  apply PadLift.gasSteps_of_raw bodySite {s with pc := UInt256.ofNat 402, stack := ret :: rest} _ hcode hfork hrun hnp body_pc.symm body_advances
  have h := PadOnlySchedule.run_template s (UInt256.ofNat 402) ret rest hstack hrun hactive hfit
  have hp : pcAfter (UInt256.ofNat 402) PadOnlySchedule.template = UInt256.ofNat 447 := by rfl
  rw [hp] at h
  exact h

def gasSteps_jump (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1022)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 447, stack := rho}
      {s with pc := UInt256.ofNat 712, stack := rho} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 447, stack := rho} _ hcode hfork hrun hnp jump_pc.symm jump_advances
  exact PadJump.run_template s (UInt256.ofNat 447) rho 712 hstack hrun (valid_merge s hcode)

def gasSteps_merge (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 712, stack := rho}
      {s with pc := UInt256.ofNat 713, stack := rho} := by
  apply PadLift.gasSteps_of_raw mergeSite {s with pc := UInt256.ofNat 712, stack := rho} _ hcode hfork hrun hnp merge_pc.symm merge_advances
  exact PadJump.run_merge s (UInt256.ofNat 712) rho hstack hrun
#print axioms gasSteps_hit
#print axioms gasSteps_miss
#print axioms gasSteps_prefix
#print axioms gasSteps_body
#print axioms gasSteps_jump
#print axioms gasSteps_merge
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadSites
