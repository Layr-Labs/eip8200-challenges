import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCoreCommon
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
structure Input where
  v0 : UInt256
  v1 : UInt256
  v2 : UInt256
  v3 : UInt256
  v4 : UInt256
  v5 : UInt256
  v6 : UInt256
  v7 : UInt256
  v8 : UInt256

def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [x.v0, x.v1, x.v2, x.v3, x.v4, x.v5, x.v6, x.v7, x.v8, UInt256.ofNat 4294967295] ++ rho
def helperTemplate : List Instr :=
  [ .op .JUMPDEST,
    .op .POP,
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295),
    .op (.Swap ⟨9, by decide⟩),
    .op .JUMP ]
theorem helper_slice :
    (Artifact.submissionArtifact.instructions.drop 3940).take helperTemplate.length = helperTemplate := by rfl
def helperSite : GenericRoundSite Artifact.submissionArtifact .Osaka helperTemplate :=
  StackSiteBuilder.ofSlice helperTemplate 3940 helper_slice
    (by change 3940 + helperTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := helperTemplate) (by decide))
    (by decide)
theorem helper_pc : helperSite.startPC = UInt256.ofNat 5168 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3940) = UInt256.ofNat 5168
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem helper_advances : ∀ instruction ∈ helperTemplate.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
theorem helper_valid (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 5168 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3940 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 3940 = 5168 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  rw [hp] at h
  rw [hcode]
  exact h
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCoreCommon
