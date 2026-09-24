import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Alignment
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Shared32Sites

abbrev template : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 63),
    .op .CALLDATASIZE,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 193),
    .op .JUMPI ]

theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 271).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 271 actual_slice
    (by change 271 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 636 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 271) = UInt256.ofNat 636
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_padding (s : State) (e : Env s) :
    Decode.isValidJumpDest s.executionEnv.code 193 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 106 = 193 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 106 (by rfl)
  rw [hpc] at h
  rw [e.code]
  exact h

def gasSteps (s : State) (e : Env s) (F : List UInt256)
    (hstack : F.length ≤ 900) (h32 : s.executionEnv.calldata.size = 32) :
    GasSteps (atState s 636 F) (atState s 193 F) := by
  apply PadLift.gasSteps_of_raw site (atState s 636 F) (atState s 193 F)
    e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have h0 : F.length < 1024 := by omega
    have h1 : F.length + 1 < 1024 := by omega
    have h2 : F.length + 2 < 1024 := by omega
    have hv := valid_padding s e
    have hn : (UInt256.land (UInt256.ofNat 32) (UInt256.ofNat 63)).toNat ≠ 0 := by decide
    simp [template, atState, runInstrSeq, DataStepper.runInstr, e.run,
      h0, h1, h2, h32, UInt256.isTrue, hv, hn]

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Alignment
