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
    (A.instructions.drop 3).take ((CachedMaskParams.leftCode 0).take 399).length =
      (CachedMaskParams.leftCode 0).take 399 := by rfl

private theorem wellFormed_left0First : ∀ instruction ∈ (CachedMaskParams.leftCode 0).take 399,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left0First : GenericRoundSite A .Osaka ((CachedMaskParams.leftCode 0).take 399) :=
  StackSiteBuilder.ofSlice _ 3 left0First_slice (by
    change 3 + ((CachedMaskParams.leftCode 0).take 399).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left0First (by decide)

private theorem left0Second_slice :
    (A.instructions.drop 882).take ((CachedMaskParams.leftCode 0).drop 399).length =
      (CachedMaskParams.leftCode 0).drop 399 := by rfl

private theorem wellFormed_left0Second : ∀ instruction ∈ (CachedMaskParams.leftCode 0).drop 399,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left0Second : GenericRoundSite A .Osaka ((CachedMaskParams.leftCode 0).drop 399) :=
  StackSiteBuilder.ofSlice _ 882 left0Second_slice (by
    change 882 + ((CachedMaskParams.leftCode 0).drop 399).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left0Second (by decide)

private theorem left2First_slice :
    (A.instructions.drop 886).take ((CachedMaskParams.leftCode 2).take 178).length =
      (CachedMaskParams.leftCode 2).take 178 := by rfl

private theorem wellFormed_left2First : ∀ instruction ∈ (CachedMaskParams.leftCode 2).take 178,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left2First : GenericRoundSite A .Osaka ((CachedMaskParams.leftCode 2).take 178) :=
  StackSiteBuilder.ofSlice _ 886 left2First_slice (by
    change 886 + ((CachedMaskParams.leftCode 2).take 178).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left2First (by decide)

private theorem left2Second_slice :
    (A.instructions.drop 1234).take (((CachedMaskParams.leftCode 2).drop 178).take 210).length =
      ((CachedMaskParams.leftCode 2).drop 178).take 210 := by rfl

private theorem wellFormed_left2Second : ∀ instruction ∈ ((CachedMaskParams.leftCode 2).drop 178).take 210,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left2Second : GenericRoundSite A .Osaka (((CachedMaskParams.leftCode 2).drop 178).take 210) :=
  StackSiteBuilder.ofSlice _ 1234 left2Second_slice (by
    change 1234 + (((CachedMaskParams.leftCode 2).drop 178).take 210).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left2Second (by decide)

private theorem left2Third_slice :
    (A.instructions.drop 2519).take ((CachedMaskParams.leftCode 2).drop 388).length =
      (CachedMaskParams.leftCode 2).drop 388 := by rfl

private theorem wellFormed_left2Third : ∀ instruction ∈ (CachedMaskParams.leftCode 2).drop 388,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left2Third : GenericRoundSite A .Osaka ((CachedMaskParams.leftCode 2).drop 388) :=
  StackSiteBuilder.ofSlice _ 2519 left2Third_slice (by
    change 2519 + ((CachedMaskParams.leftCode 2).drop 388).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left2Third (by decide)

private theorem rightFirst_slice :
    (A.instructions.drop 451).take (CachedMaskParams.rightCode.take 373).length =
      CachedMaskParams.rightCode.take 373 := by rfl

private theorem wellFormed_rightFirst : ∀ instruction ∈ CachedMaskParams.rightCode.take 373,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def rightFirst : GenericRoundSite A .Osaka (CachedMaskParams.rightCode.take 373) :=
  StackSiteBuilder.ofSlice _ 451 rightFirst_slice (by
    change 451 + (CachedMaskParams.rightCode.take 373).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_rightFirst (by decide)

private theorem rightSecond_slice :
    (A.instructions.drop 2489).take (CachedMaskParams.rightCode.drop 373).length =
      CachedMaskParams.rightCode.drop 373 := by rfl

private theorem wellFormed_rightSecond : ∀ instruction ∈ CachedMaskParams.rightCode.drop 373,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def rightSecond : GenericRoundSite A .Osaka (CachedMaskParams.rightCode.drop 373) :=
  StackSiteBuilder.ofSlice _ 2489 rightSecond_slice (by
    change 2489 + (CachedMaskParams.rightCode.drop 373).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_rightSecond (by decide)

private theorem left4First_slice :
    (A.instructions.drop 1611).take ((CachedMaskParams.leftCode 4).take 213).length =
      (CachedMaskParams.leftCode 4).take 213 := by rfl

private theorem wellFormed_left4First : ∀ instruction ∈ (CachedMaskParams.leftCode 4).take 213,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left4First : GenericRoundSite A .Osaka ((CachedMaskParams.leftCode 4).take 213) :=
  StackSiteBuilder.ofSlice _ 1611 left4First_slice (by
    change 1611 + ((CachedMaskParams.leftCode 4).take 213).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left4First (by decide)

private theorem left4Second_slice :
    (A.instructions.drop 2582).take (((CachedMaskParams.leftCode 4).drop 213).take 97).length =
      ((CachedMaskParams.leftCode 4).drop 213).take 97 := by rfl

private theorem wellFormed_left4Second : ∀ instruction ∈ ((CachedMaskParams.leftCode 4).drop 213).take 97,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left4Second : GenericRoundSite A .Osaka (((CachedMaskParams.leftCode 4).drop 213).take 97) :=
  StackSiteBuilder.ofSlice _ 2582 left4Second_slice (by
    change 2582 + (((CachedMaskParams.leftCode 4).drop 213).take 97).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left4Second (by decide)

private theorem left4Third_slice :
    (A.instructions.drop 2731).take (((CachedMaskParams.leftCode 4).drop 310).take 54).length =
      ((CachedMaskParams.leftCode 4).drop 310).take 54 := by rfl

private theorem wellFormed_left4Third : ∀ instruction ∈ ((CachedMaskParams.leftCode 4).drop 310).take 54,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left4Third : GenericRoundSite A .Osaka (((CachedMaskParams.leftCode 4).drop 310).take 54) :=
  StackSiteBuilder.ofSlice _ 2731 left4Third_slice (by
    change 2731 + (((CachedMaskParams.leftCode 4).drop 310).take 54).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left4Third (by decide)

private theorem left4Fourth_slice :
    (A.instructions.drop 2840).take ((CachedMaskParams.leftCode 4).drop 364).length =
      (CachedMaskParams.leftCode 4).drop 364 := by rfl

private theorem wellFormed_left4Fourth : ∀ instruction ∈ (CachedMaskParams.leftCode 4).drop 364,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def left4Fourth : GenericRoundSite A .Osaka ((CachedMaskParams.leftCode 4).drop 364) :=
  StackSiteBuilder.ofSlice _ 2840 left4Fourth_slice (by
    change 2840 + ((CachedMaskParams.leftCode 4).drop 364).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_left4Fourth (by decide)

private def exactSite (index : Nat) (instruction : Instr)
    (atIndex : A.instructions[index]? = some instruction)
    (wellFormed : Stepper.WellFormed .Osaka instruction) : LocatedSite A .Osaka where
  located := ⟨index, instruction, atIndex, wellFormed⟩
  pc := UInt256.ofNat (A.instructionPC index)
  pc_eq := pc_toNat index


def left0Entry : Bridge A .Osaka where
  push := exactSite 879 (.push 2 (UInt256.ofNat 4)) (by rfl) (by decide)
  jump := exactSite 880 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
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
  push := exactSite 402 (.push 2 (UInt256.ofNat 1092)) (by rfl) (by decide)
  jump := exactSite 403 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 881 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 883 (.push 2 (UInt256.ofNat 1331)) (by rfl) (by decide)
  jump := exactSite 884 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1066 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 1231 (.push 2 (UInt256.ofNat 1098)) (by rfl) (by decide)
  jump := exactSite 1232 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 885 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 1064 (.push 2 (UInt256.ofNat 1661)) (by rfl) (by decide)
  jump := exactSite 1065 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1233 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 1444 (.push 2 (UInt256.ofNat 3958)) (by rfl) (by decide)
  jump := exactSite 1445 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2518 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 2579 (.push 2 (UInt256.ofNat 1937)) (by rfl) (by decide)
  jump := exactSite 2580 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1446 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 2486 (.push 2 (UInt256.ofNat 541)) (by rfl) (by decide)
  jump := exactSite 2487 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 450 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 824 (.push 2 (UInt256.ofNat 3922)) (by rfl) (by decide)
  jump := exactSite 825 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2488 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 2516 (.push 2 (UInt256.ofNat 4169)) (by rfl) (by decide)
  jump := exactSite 2517 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2681 (.op .JUMPDEST) (by rfl)
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

def left4Bridge1 : Bridge A .Osaka where
  push := exactSite 1824 (.push 2 (UInt256.ofNat 4040)) (by rfl) (by decide)
  jump := exactSite 1825 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2581 (.op .JUMPDEST) (by rfl)
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

def left4Bridge2 : Bridge A .Osaka where
  push := exactSite 2679 (.push 2 (UInt256.ofNat 4228)) (by rfl) (by decide)
  jump := exactSite 2680 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2730 (.op .JUMPDEST) (by rfl)
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

def left4Bridge3 : Bridge A .Osaka where
  push := exactSite 2785 (.push 2 (UInt256.ofNat 4500)) (by rfl) (by decide)
  jump := exactSite 2786 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2839 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 2924 (.push 2 (UInt256.ofNat 2544)) (by rfl) (by decide)
  jump := exactSite 2925 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1826 (.op .JUMPDEST) (by rfl)
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
