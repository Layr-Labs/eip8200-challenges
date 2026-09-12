import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Dispatch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80PadJump
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
def jumpTemplate : List Instr := PadJump.template 1058
theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 307).take jumpTemplate.length = jumpTemplate := by rfl
def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpTemplate :=
  StackSiteBuilder.ofSlice jumpTemplate 307 jump_slice
    (by change 307 + jumpTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := jumpTemplate) (by decide))
    (by decide)
theorem jump_pc : jumpSite.startPC = UInt256.ofNat 502 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 307) = UInt256.ofNat 502
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem jump_advances : ∀ instruction ∈ jumpTemplate.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem valid_merge (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 1048).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 668 = 1048 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 668 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 1048 = true
  rw [hcode]
  exact h

def gasSteps_jump (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1022)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 502, stack := rho}
      {s with pc := UInt256.ofNat 1048, stack := rho} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 502, stack := rho} _ hcode hfork hrun hnp jump_pc.symm jump_advances
  exact PadJump.run_template s (UInt256.ofNat 502) rho 1058 hstack hrun (valid_merge s hcode)

#print axioms gasSteps_jump
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80PadJump
