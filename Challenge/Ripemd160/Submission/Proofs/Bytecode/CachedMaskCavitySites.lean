import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantSites
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
    (A.instructions.drop 363).take (CachedMaskParams.leftCode 0).length =
      CachedMaskParams.leftCode 0 := by rfl

private theorem wellFormed_left0First : ∀ instruction ∈ CachedMaskParams.leftCode 0,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left0First : GenericRoundSite A .Osaka (CachedMaskParams.leftCode 0) :=
  StackSiteBuilder.ofSlice _ 363 left0First_slice (by
    change 363 + (CachedMaskParams.leftCode 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left0First (by decide)

abbrev left2First := CallsConstantSites.left2
abbrev left4First := CallsConstantSites.left4

private theorem rightFirst_slice :
    (A.instructions.drop 3559).take CachedMaskParams.rightCode.length =
      CachedMaskParams.rightCode := by rfl

private theorem wellFormed_rightFirst : ∀ instruction ∈ CachedMaskParams.rightCode,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def rightFirst : GenericRoundSite A .Osaka CachedMaskParams.rightCode :=
  StackSiteBuilder.ofSlice _ 3559 rightFirst_slice (by
    change 3559 + CachedMaskParams.rightCode.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_rightFirst (by decide)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
