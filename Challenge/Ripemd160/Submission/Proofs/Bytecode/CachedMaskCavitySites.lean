import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open CavityQuadGroup
open StackRoundTemplate

abbrev A := Artifact.submissionArtifact

theorem code_bound : A.code.size < UInt256.size := by
  change submissionBytecode.size < UInt256.size
  rw [referenceBytecode_size]
  decide

theorem pc_toNat (index : Nat) :
    (UInt256.ofNat (A.instructionPC index)).toNat = A.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
    (A.instructionPC_le_code_size index) code_bound)

private theorem left0First_slice :
    (A.instructions.drop 331).take (CachedMaskParams.leftCode 0).length =
      CachedMaskParams.leftCode 0 := by rfl

private theorem wellFormed_left0First : ∀ instruction ∈ CachedMaskParams.leftCode 0,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left0First : GenericRoundSite A .Osaka (CachedMaskParams.leftCode 0) :=
  StackSiteBuilder.ofSlice _ 331 left0First_slice (by
    change 331 + (CachedMaskParams.leftCode 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left0First (by decide)

private theorem left2First_slice :
    (A.instructions.drop 904).take (CachedMaskParams.leftCode 2).length =
      CachedMaskParams.leftCode 2 := by rfl

private theorem wellFormed_left2First : ∀ instruction ∈ CachedMaskParams.leftCode 2,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left2First : GenericRoundSite A .Osaka (CachedMaskParams.leftCode 2) :=
  StackSiteBuilder.ofSlice _ 904 left2First_slice (by
    change 904 + (CachedMaskParams.leftCode 2).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left2First (by decide)

private theorem rightFirst_slice :
    (A.instructions.drop 3238).take CachedMaskParams.rightCode.length =
      CachedMaskParams.rightCode := by rfl

private theorem wellFormed_rightFirst : ∀ instruction ∈ CachedMaskParams.rightCode,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def rightFirst : GenericRoundSite A .Osaka CachedMaskParams.rightCode :=
  StackSiteBuilder.ofSlice _ 3238 rightFirst_slice (by
    change 3238 + CachedMaskParams.rightCode.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_rightFirst (by decide)

private theorem left4First_slice :
    (A.instructions.drop 1525).take (CachedMaskParams.leftCode 4).length =
      CachedMaskParams.leftCode 4 := by rfl

private theorem wellFormed_left4First : ∀ instruction ∈ CachedMaskParams.leftCode 4,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left4First : GenericRoundSite A .Osaka (CachedMaskParams.leftCode 4) :=
  StackSiteBuilder.ofSlice _ 1525 left4First_slice (by
    change 1525 + (CachedMaskParams.leftCode 4).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left4First (by decide)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
