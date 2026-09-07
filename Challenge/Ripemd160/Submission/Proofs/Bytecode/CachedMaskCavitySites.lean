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

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩




private theorem left0First_slice :
    (A.instructions.drop 3).take (CachedMaskParams.leftCode 0).length =
      CachedMaskParams.leftCode 0 := by rfl

private theorem wellFormed_left0First : ∀ instruction ∈ CachedMaskParams.leftCode 0,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left0First : GenericRoundSite A .Osaka (CachedMaskParams.leftCode 0) :=
  StackSiteBuilder.ofSlice _ 3 left0First_slice (by
    change 3 + (CachedMaskParams.leftCode 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left0First (by decide)

private theorem left2First_slice :
    (A.instructions.drop 910).take (CachedMaskParams.leftCode 2).length =
      CachedMaskParams.leftCode 2 := by rfl

private theorem wellFormed_left2First : ∀ instruction ∈ CachedMaskParams.leftCode 2,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left2First : GenericRoundSite A .Osaka (CachedMaskParams.leftCode 2) :=
  StackSiteBuilder.ofSlice _ 910 left2First_slice (by
    change 910 + (CachedMaskParams.leftCode 2).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left2First (by decide)

private theorem rightFirst_slice :
    (A.instructions.drop 452).take CachedMaskParams.rightCode.length =
      CachedMaskParams.rightCode := by rfl

private theorem wellFormed_rightFirst : ∀ instruction ∈ CachedMaskParams.rightCode,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def rightFirst : GenericRoundSite A .Osaka CachedMaskParams.rightCode :=
  StackSiteBuilder.ofSlice _ 452 rightFirst_slice (by
    change 452 + CachedMaskParams.rightCode.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_rightFirst (by decide)

private theorem left4First_slice :
    (A.instructions.drop 1692).take (CachedMaskParams.leftCode 4).length =
      CachedMaskParams.leftCode 4 := by rfl

private theorem wellFormed_left4First : ∀ instruction ∈ CachedMaskParams.leftCode 4,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left4First : GenericRoundSite A .Osaka (CachedMaskParams.leftCode 4) :=
  StackSiteBuilder.ofSlice _ 1692 left4First_slice (by
    change 1692 + (CachedMaskParams.leftCode 4).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left4First (by decide)

private def exactSite (index : Nat) (instruction : Instr)
    (atIndex : A.instructions[index]? = some instruction)
    (wellFormed : Stepper.WellFormed .Osaka instruction) : LocatedSite A .Osaka where
  located := ⟨index, instruction, atIndex, wellFormed⟩
  pc := UInt256.ofNat (A.instructionPC index)
  pc_eq := pc_toNat index


def left0Entry : Bridge A .Osaka where
  push := exactSite 907 (.push 2 (UInt256.ofNat 4)) (by rfl) (by decide)
  jump := exactSite 908 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2 (.op .JUMPDEST) (by rfl)
    (wfOp (by decide) trivial rfl)
  push_instr := by
    simp only [exactSite]
    apply congrArg (Instr.push ⟨2, by decide⟩)
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  jump_instr := rfl
  destination_instr := rfl
  jump_at := by
    simp only [exactSite]
    repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide

def left0Return : Bridge A .Osaka where
  push := exactSite 403 (.push 2 (UInt256.ofNat 1705)) (by rfl) (by decide)
  jump := exactSite 404 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1360 (.op .JUMPDEST) (by rfl)
    (wfOp (by decide) trivial rfl)
  push_instr := by
    simp only [exactSite]
    apply congrArg (Instr.push ⟨2, by decide⟩)
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  jump_instr := rfl
  destination_instr := rfl
  jump_at := by
    simp only [exactSite]
    repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide

def left2Entry : Bridge A .Osaka where
  push := exactSite 1525 (.push 2 (UInt256.ofNat 1124)) (by rfl) (by decide)
  jump := exactSite 1526 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 909 (.op .JUMPDEST) (by rfl)
    (wfOp (by decide) trivial rfl)
  push_instr := by
    simp only [exactSite]
    apply congrArg (Instr.push ⟨2, by decide⟩)
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  jump_instr := rfl
  destination_instr := rfl
  jump_at := by
    simp only [exactSite]
    repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide

def left2Return : Bridge A .Osaka where
  push := exactSite 1358 (.push 2 (UInt256.ofNat 2035)) (by rfl) (by decide)
  jump := exactSite 1359 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1527 (.op .JUMPDEST) (by rfl)
    (wfOp (by decide) trivial rfl)
  push_instr := by
    simp only [exactSite]
    apply congrArg (Instr.push ⟨2, by decide⟩)
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  jump_instr := rfl
  destination_instr := rfl
  jump_at := by
    simp only [exactSite]
    repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide

def rightEntry : Bridge A .Osaka where
  push := exactSite 2902 (.push 2 (UInt256.ofNat 542)) (by rfl) (by decide)
  jump := exactSite 2903 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 451 (.op .JUMPDEST) (by rfl)
    (wfOp (by decide) trivial rfl)
  push_instr := by
    simp only [exactSite]
    apply congrArg (Instr.push ⟨2, by decide⟩)
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  jump_instr := rfl
  destination_instr := rfl
  jump_at := by
    simp only [exactSite]
    repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide

def rightReturn : Bridge A .Osaka where
  push := exactSite 852 (.push 2 (UInt256.ofNat 4416)) (by rfl) (by decide)
  jump := exactSite 853 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2904 (.op .JUMPDEST) (by rfl)
    (wfOp (by decide) trivial rfl)
  push_instr := by
    simp only [exactSite]
    apply congrArg (Instr.push ⟨2, by decide⟩)
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  jump_instr := rfl
  destination_instr := rfl
  jump_at := by
    simp only [exactSite]
    repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide

def left4Return : Bridge A .Osaka where
  push := exactSite 2140 (.push 2 (UInt256.ofNat 2942)) (by rfl) (by decide)
  jump := exactSite 2141 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2142 (.op .JUMPDEST) (by rfl)
    (wfOp (by decide) trivial rfl)
  push_instr := by
    simp only [exactSite]
    apply congrArg (Instr.push ⟨2, by decide⟩)
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  jump_instr := rfl
  destination_instr := rfl
  jump_at := by
    simp only [exactSite]
    repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
