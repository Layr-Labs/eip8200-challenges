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
    (A.instructions.drop 3).take ((CachedMaskParams.leftCode 0).take 407).length =
      (CachedMaskParams.leftCode 0).take 407 := by rfl

private theorem wellFormed_left0First : ∀ instruction ∈ (CachedMaskParams.leftCode 0).take 407,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left0First : GenericRoundSite A .Osaka ((CachedMaskParams.leftCode 0).take 407) :=
  StackSiteBuilder.ofSlice _ 3 left0First_slice (by
    change 3 + ((CachedMaskParams.leftCode 0).take 407).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left0First (by decide)

private theorem left0Second_slice :
    (A.instructions.drop 1109).take ((CachedMaskParams.leftCode 0).drop 407).length =
      (CachedMaskParams.leftCode 0).drop 407 := by rfl

private theorem wellFormed_left0Second : ∀ instruction ∈ (CachedMaskParams.leftCode 0).drop 407,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left0Second : GenericRoundSite A .Osaka ((CachedMaskParams.leftCode 0).drop 407) :=
  StackSiteBuilder.ofSlice _ 1109 left0Second_slice (by
    change 1109 + ((CachedMaskParams.leftCode 0).drop 407).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left0Second (by decide)

private theorem left2First_slice :
    (A.instructions.drop 1113).take ((CachedMaskParams.leftCode 2).take 181).length =
      (CachedMaskParams.leftCode 2).take 181 := by rfl

private theorem wellFormed_left2First : ∀ instruction ∈ (CachedMaskParams.leftCode 2).take 181,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left2First : GenericRoundSite A .Osaka ((CachedMaskParams.leftCode 2).take 181) :=
  StackSiteBuilder.ofSlice _ 1113 left2First_slice (by
    change 1113 + ((CachedMaskParams.leftCode 2).take 181).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left2First (by decide)

private theorem left2Second_slice :
    (A.instructions.drop 1463).take (((CachedMaskParams.leftCode 2).drop 181).take 210).length =
      ((CachedMaskParams.leftCode 2).drop 181).take 210 := by rfl

private theorem wellFormed_left2Second : ∀ instruction ∈ ((CachedMaskParams.leftCode 2).drop 181).take 210,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left2Second : GenericRoundSite A .Osaka (((CachedMaskParams.leftCode 2).drop 181).take 210) :=
  StackSiteBuilder.ofSlice _ 1463 left2Second_slice (by
    change 1463 + (((CachedMaskParams.leftCode 2).drop 181).take 210).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left2Second (by decide)

private theorem left2Third_slice :
    (A.instructions.drop 2681).take ((CachedMaskParams.leftCode 2).drop 391).length =
      (CachedMaskParams.leftCode 2).drop 391 := by rfl

private theorem wellFormed_left2Third : ∀ instruction ∈ (CachedMaskParams.leftCode 2).drop 391,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left2Third : GenericRoundSite A .Osaka ((CachedMaskParams.leftCode 2).drop 391) :=
  StackSiteBuilder.ofSlice _ 2681 left2Third_slice (by
    change 2681 + ((CachedMaskParams.leftCode 2).drop 391).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left2Third (by decide)

private theorem rightFirst_slice :
    (A.instructions.drop 474).take (CachedMaskParams.rightCode.take 380).length =
      CachedMaskParams.rightCode.take 380 := by rfl

private theorem wellFormed_rightFirst : ∀ instruction ∈ CachedMaskParams.rightCode.take 380,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def rightFirst : GenericRoundSite A .Osaka (CachedMaskParams.rightCode.take 380) :=
  StackSiteBuilder.ofSlice _ 474 rightFirst_slice (by
    change 474 + (CachedMaskParams.rightCode.take 380).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_rightFirst (by decide)

private theorem rightSecond_slice :
    (A.instructions.drop 2650).take (CachedMaskParams.rightCode.drop 380).length =
      CachedMaskParams.rightCode.drop 380 := by rfl

private theorem wellFormed_rightSecond : ∀ instruction ∈ CachedMaskParams.rightCode.drop 380,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def rightSecond : GenericRoundSite A .Osaka (CachedMaskParams.rightCode.drop 380) :=
  StackSiteBuilder.ofSlice _ 2650 rightSecond_slice (by
    change 2650 + (CachedMaskParams.rightCode.drop 380).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_rightSecond (by decide)

private def exactSite (index : Nat) (instruction : Instr)
    (atIndex : A.instructions[index]? = some instruction)
    (wellFormed : Stepper.WellFormed .Osaka instruction) : LocatedSite A .Osaka where
  located := ⟨index, instruction, atIndex, wellFormed⟩
  pc := UInt256.ofNat (A.instructionPC index)
  pc_eq := pc_toNat index


def left0Entry : Bridge A .Osaka where
  push := exactSite 1106 (.push 2 (UInt256.ofNat 4)) (by rfl) (by decide)
  jump := exactSite 1107 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
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

def left0Bridge1 : Bridge A .Osaka where
  push := exactSite 410 (.push 2 (UInt256.ofNat 1346)) (by rfl) (by decide)
  jump := exactSite 411 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1108 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 1110 (.push 2 (UInt256.ofNat 1589)) (by rfl) (by decide)
  jump := exactSite 1111 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1297 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 1460 (.push 2 (UInt256.ofNat 1352)) (by rfl) (by decide)
  jump := exactSite 1461 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1112 (.op .JUMPDEST) (by rfl)
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

def left2Bridge1 : Bridge A .Osaka where
  push := exactSite 1294 (.push 2 (UInt256.ofNat 1917)) (by rfl) (by decide)
  jump := exactSite 1295 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1462 (.op .JUMPDEST) (by rfl)
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

def left2Bridge2 : Bridge A .Osaka where
  push := exactSite 1673 (.push 2 (UInt256.ofNat 4243)) (by rfl) (by decide)
  jump := exactSite 1674 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2680 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 2746 (.push 2 (UInt256.ofNat 2193)) (by rfl) (by decide)
  jump := exactSite 2747 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1675 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 2647 (.push 2 (UInt256.ofNat 561)) (by rfl) (by decide)
  jump := exactSite 2648 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 473 (.op .JUMPDEST) (by rfl)
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

def rightBridge1 : Bridge A .Osaka where
  push := exactSite 854 (.push 2 (UInt256.ofNat 4206)) (by rfl) (by decide)
  jump := exactSite 855 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2649 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 2678 (.push 2 (UInt256.ofNat 4330)) (by rfl) (by decide)
  jump := exactSite 2679 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2748 (.op .JUMPDEST) (by rfl)
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
