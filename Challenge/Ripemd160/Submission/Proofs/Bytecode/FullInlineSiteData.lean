import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open CavityQuadGroup StackRoundTemplate
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
private def exactSite (index : Nat) (instruction : Instr)
    (atIndex : A.instructions[index]? = some instruction)
    (wellFormed : Stepper.WellFormed .Osaka instruction) : LocatedSite A .Osaka where
  located := ⟨index, instruction, atIndex, wellFormed⟩
  pc := UInt256.ofNat (A.instructionPC index)
  pc_eq := pc_toNat index

def left0 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 0) 0) :=
  StackSiteBuilder.ofSlice _ 3147 (by rfl) (by
    change 3147 + (CachedMaskQuadGroup.code (FullInlineParams.left 0) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left1 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 1) 0) :=
  StackSiteBuilder.ofSlice _ 3247 (by rfl) (by
    change 3247 + (CachedMaskQuadGroup.code (FullInlineParams.left 1) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left2 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 2) 0) :=
  StackSiteBuilder.ofSlice _ 3347 (by rfl) (by
    change 3347 + (CachedMaskQuadGroup.code (FullInlineParams.left 2) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left3 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 3) 0) :=
  StackSiteBuilder.ofSlice _ 3447 (by rfl) (by
    change 3447 + (CachedMaskQuadGroup.code (FullInlineParams.left 3) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left4 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 4) 0) :=
  StackSiteBuilder.ofSlice _ 3547 (by rfl) (by
    change 3547 + (CachedMaskQuadGroup.code (FullInlineParams.left 4) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left5 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 5) 0) :=
  StackSiteBuilder.ofSlice _ 3663 (by rfl) (by
    change 3663 + (CachedMaskQuadGroup.code (FullInlineParams.left 5) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left6 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 6) 0) :=
  StackSiteBuilder.ofSlice _ 3779 (by rfl) (by
    change 3779 + (CachedMaskQuadGroup.code (FullInlineParams.left 6) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left7 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 7) 0) :=
  StackSiteBuilder.ofSlice _ 3895 (by rfl) (by
    change 3895 + (CachedMaskQuadGroup.code (FullInlineParams.left 7) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left8 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 8) 0) :=
  StackSiteBuilder.ofSlice _ 4011 (by rfl) (by
    change 4011 + (CachedMaskQuadGroup.code (FullInlineParams.left 8) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left9 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 9) 0) :=
  StackSiteBuilder.ofSlice _ 4123 (by rfl) (by
    change 4123 + (CachedMaskQuadGroup.code (FullInlineParams.left 9) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left10 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 10) 0) :=
  StackSiteBuilder.ofSlice _ 4235 (by rfl) (by
    change 4235 + (CachedMaskQuadGroup.code (FullInlineParams.left 10) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left11 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 11) 0) :=
  StackSiteBuilder.ofSlice _ 4347 (by rfl) (by
    change 4347 + (CachedMaskQuadGroup.code (FullInlineParams.left 11) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left12 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 12) 0) :=
  StackSiteBuilder.ofSlice _ 4459 (by rfl) (by
    change 4459 + (CachedMaskQuadGroup.code (FullInlineParams.left 12) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left13 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 13) 0) :=
  StackSiteBuilder.ofSlice _ 4575 (by rfl) (by
    change 4575 + (CachedMaskQuadGroup.code (FullInlineParams.left 13) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left14 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 14) 0) :=
  StackSiteBuilder.ofSlice _ 4691 (by rfl) (by
    change 4691 + (CachedMaskQuadGroup.code (FullInlineParams.left 14) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left15 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 15) 0) :=
  StackSiteBuilder.ofSlice _ 4807 (by rfl) (by
    change 4807 + (CachedMaskQuadGroup.code (FullInlineParams.left 15) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left16 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 16) 0) :=
  StackSiteBuilder.ofSlice _ 4923 (by rfl) (by
    change 4923 + (CachedMaskQuadGroup.code (FullInlineParams.left 16) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left17 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 17) 0) :=
  StackSiteBuilder.ofSlice _ 5035 (by rfl) (by
    change 5035 + (CachedMaskQuadGroup.code (FullInlineParams.left 17) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left18 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 18) 0) :=
  StackSiteBuilder.ofSlice _ 5147 (by rfl) (by
    change 5147 + (CachedMaskQuadGroup.code (FullInlineParams.left 18) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def left19 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left 19) 0) :=
  StackSiteBuilder.ofSlice _ 5259 (by rfl) (by
    change 5259 + (CachedMaskQuadGroup.code (FullInlineParams.left 19) 0).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)


def right0 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 0) 5) :=
  StackSiteBuilder.ofSlice _ 5374 (by rfl) (by
    change 5374 + (CachedMaskQuadGroup.code (FullInlineParams.right 0) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right1 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 1) 5) :=
  StackSiteBuilder.ofSlice _ 5486 (by rfl) (by
    change 5486 + (CachedMaskQuadGroup.code (FullInlineParams.right 1) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right2 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 2) 5) :=
  StackSiteBuilder.ofSlice _ 5598 (by rfl) (by
    change 5598 + (CachedMaskQuadGroup.code (FullInlineParams.right 2) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right3 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 3) 5) :=
  StackSiteBuilder.ofSlice _ 5710 (by rfl) (by
    change 5710 + (CachedMaskQuadGroup.code (FullInlineParams.right 3) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right4 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 4) 5) :=
  StackSiteBuilder.ofSlice _ 5822 (by rfl) (by
    change 5822 + (CachedMaskQuadGroup.code (FullInlineParams.right 4) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right5 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 5) 5) :=
  StackSiteBuilder.ofSlice _ 5938 (by rfl) (by
    change 5938 + (CachedMaskQuadGroup.code (FullInlineParams.right 5) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right6 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 6) 5) :=
  StackSiteBuilder.ofSlice _ 6054 (by rfl) (by
    change 6054 + (CachedMaskQuadGroup.code (FullInlineParams.right 6) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right7 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 7) 5) :=
  StackSiteBuilder.ofSlice _ 6170 (by rfl) (by
    change 6170 + (CachedMaskQuadGroup.code (FullInlineParams.right 7) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right8 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 8) 5) :=
  StackSiteBuilder.ofSlice _ 6286 (by rfl) (by
    change 6286 + (CachedMaskQuadGroup.code (FullInlineParams.right 8) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right9 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 9) 5) :=
  StackSiteBuilder.ofSlice _ 6398 (by rfl) (by
    change 6398 + (CachedMaskQuadGroup.code (FullInlineParams.right 9) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right10 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 10) 5) :=
  StackSiteBuilder.ofSlice _ 6510 (by rfl) (by
    change 6510 + (CachedMaskQuadGroup.code (FullInlineParams.right 10) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right11 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 11) 5) :=
  StackSiteBuilder.ofSlice _ 6622 (by rfl) (by
    change 6622 + (CachedMaskQuadGroup.code (FullInlineParams.right 11) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right12 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 12) 5) :=
  StackSiteBuilder.ofSlice _ 6734 (by rfl) (by
    change 6734 + (CachedMaskQuadGroup.code (FullInlineParams.right 12) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right13 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 13) 5) :=
  StackSiteBuilder.ofSlice _ 6850 (by rfl) (by
    change 6850 + (CachedMaskQuadGroup.code (FullInlineParams.right 13) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right14 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 14) 5) :=
  StackSiteBuilder.ofSlice _ 6966 (by rfl) (by
    change 6966 + (CachedMaskQuadGroup.code (FullInlineParams.right 14) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right15 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 15) 5) :=
  StackSiteBuilder.ofSlice _ 7082 (by rfl) (by
    change 7082 + (CachedMaskQuadGroup.code (FullInlineParams.right 15) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right16 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 16) 5) :=
  StackSiteBuilder.ofSlice _ 7198 (by rfl) (by
    change 7198 + (CachedMaskQuadGroup.code (FullInlineParams.right 16) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right17 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 17) 5) :=
  StackSiteBuilder.ofSlice _ 7298 (by rfl) (by
    change 7298 + (CachedMaskQuadGroup.code (FullInlineParams.right 17) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right18 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 18) 5) :=
  StackSiteBuilder.ofSlice _ 7398 (by rfl) (by
    change 7398 + (CachedMaskQuadGroup.code (FullInlineParams.right 18) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

def right19 : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right 19) 5) :=
  StackSiteBuilder.ofSlice _ 7498 (by rfl) (by
    change 7498 + (CachedMaskQuadGroup.code (FullInlineParams.right 19) 5).length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) code_bound (StackRoundData.templateWellFormed_mem (by decide)) (by decide)


def leftEntry : Bridge A .Osaka where
  push := exactSite 907 (.push 2 5233) (by rfl) (by decide)
  jump := exactSite 908 (.op .JUMP) (by rfl) ⟨by decide, trivial, rfl⟩
  destination := exactSite 3146 (.op .JUMPDEST) (by rfl) ⟨by decide, trivial, rfl⟩
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
  push := exactSite 2154 (.push 2 8038) (by rfl) (by decide)
  jump := exactSite 2155 (.op .JUMP) (by rfl) ⟨by decide, trivial, rfl⟩
  destination := exactSite 5373 (.op .JUMPDEST) (by rfl) ⟨by decide, trivial, rfl⟩
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
  push := exactSite 5371 (.push 2 2942) (by rfl) (by decide)
  jump := exactSite 5372 (.op .JUMP) (by rfl) ⟨by decide, trivial, rfl⟩
  destination := exactSite 2142 (.op .JUMPDEST) (by rfl) ⟨by decide, trivial, rfl⟩
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
  push := exactSite 7598 (.push 2 4320) (by rfl) (by decide)
  jump := exactSite 7599 (.op .JUMP) (by rfl) ⟨by decide, trivial, rfl⟩
  destination := exactSite 2804 (.op .JUMPDEST) (by rfl) ⟨by decide, trivial, rfl⟩
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSites
