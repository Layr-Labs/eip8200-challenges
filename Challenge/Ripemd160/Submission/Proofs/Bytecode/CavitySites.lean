import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavitySites

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

private theorem leftFirst_slice :
    (A.instructions.drop 3).take (CavityParams.leftCode.take 320).length =
      CavityParams.leftCode.take 320 := by rfl

private theorem wellFormed_leftFirst : ∀ instruction ∈ CavityParams.leftCode.take 320,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def leftFirst : GenericRoundSite A .Osaka (CavityParams.leftCode.take 320) :=
  StackSiteBuilder.ofSlice _ 3 leftFirst_slice (by
    change 3 + (CavityParams.leftCode.take 320).length ≤
      Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_leftFirst (by decide)

private theorem leftSecond_slice :
    (A.instructions.drop 940).take (CavityParams.leftCode.drop 320).length =
      CavityParams.leftCode.drop 320 := by rfl

private theorem wellFormed_leftSecond : ∀ instruction ∈ CavityParams.leftCode.drop 320,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def leftSecond : GenericRoundSite A .Osaka (CavityParams.leftCode.drop 320) :=
  StackSiteBuilder.ofSlice _ 940 leftSecond_slice (by
    change 940 + (CavityParams.leftCode.drop 320).length ≤
      Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_leftSecond (by decide)

private theorem rightFirst_slice :
    (A.instructions.drop 387).take (CavityParams.rightCode.take 298).length =
      CavityParams.rightCode.take 298 := by rfl

private theorem wellFormed_rightFirst : ∀ instruction ∈ CavityParams.rightCode.take 298,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def rightFirst : GenericRoundSite A .Osaka (CavityParams.rightCode.take 298) :=
  StackSiteBuilder.ofSlice _ 387 rightFirst_slice (by
    change 387 + (CavityParams.rightCode.take 298).length ≤
      Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_rightFirst (by decide)

private theorem rightSecond_slice :
    (A.instructions.drop 2478).take (CavityParams.rightCode.drop 298).length =
      CavityParams.rightCode.drop 298 := by rfl

private theorem wellFormed_rightSecond : ∀ instruction ∈ CavityParams.rightCode.drop 298,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def rightSecond : GenericRoundSite A .Osaka (CavityParams.rightCode.drop 298) :=
  StackSiteBuilder.ofSlice _ 2478 rightSecond_slice (by
    change 2482 + (CavityParams.rightCode.drop 298).length ≤
      Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound wellFormed_rightSecond (by decide)

private def exactSite (index : Nat) (instruction : Instr)
    (atIndex : A.instructions[index]? = some instruction)
    (wellFormed : Stepper.WellFormed .Osaka instruction) : LocatedSite A .Osaka where
  located := ⟨index, instruction, atIndex, wellFormed⟩
  pc := UInt256.ofNat (A.instructionPC index)
  pc_eq := pc_toNat index


def leftEntry : Bridge A .Osaka where
  push := exactSite 937 (.push 2 (UInt256.ofNat 4)) (by rfl) (by decide)
  jump := exactSite 938 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
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

def leftBridge1 : Bridge A .Osaka where
  push := exactSite 323 (.push 2 (UInt256.ofNat 1341)) (by rfl) (by decide)
  jump := exactSite 324 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 939 (.op .JUMPDEST) (by rfl)
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

def leftReturn : Bridge A .Osaka where
  push := exactSite 1028 (.push 2 (UInt256.ofNat 1589)) (by rfl) (by decide)
  jump := exactSite 1029 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 1115 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 2479 (.push 2 (UInt256.ofNat 561)) (by rfl) (by decide)
  jump := exactSite 2480 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 386 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 685 (.push 2 (UInt256.ofNat 3874)) (by rfl) (by decide)
  jump := exactSite 686 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2481 (.op .JUMPDEST) (by rfl)
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
  push := exactSite 2592 (.push 2 (UInt256.ofNat 4122)) (by rfl) (by decide)
  jump := exactSite 2593 (.op .JUMP) (by rfl) (wfOp (by decide) trivial rfl)
  destination := exactSite 2603 (.op .JUMPDEST) (by rfl)
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavitySites
