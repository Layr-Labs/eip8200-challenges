import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcSizeGuard
import Challenge.Ripemd160.Submission.Local20261028.RecPatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Local20261028.RecGuardInstructionWindow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuardLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.Ripemd160.Submission.Local20261028.ColdExecution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.AbcArm
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open TinyGuardLogic
abbrev Located := DataStepper.Located Control.Artifact.submissionArtifact .Osaka

@[simp] theorem pc_176 : Control.Artifact.submissionArtifact.instructionPC 6096 = 8085 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4095 : Control.Artifact.submissionArtifact.instructionPC 6203 = 8329 := by
  exact Control.GuardInstructionWindow.pc 0
@[simp] theorem pc_4096 : Control.Artifact.submissionArtifact.instructionPC 6204 = 8362 := by
  exact Control.GuardInstructionWindow.pc 1
@[simp] theorem pc_4097 : Control.Artifact.submissionArtifact.instructionPC 6205 = 8363 := by
  exact Control.GuardInstructionWindow.pc 2
@[simp] theorem pc_4098 : Control.Artifact.submissionArtifact.instructionPC 6206 = 8364 := by
  exact Control.GuardInstructionWindow.pc 3
@[simp] theorem pc_4101 : Control.Artifact.submissionArtifact.instructionPC 6207 = 8365 := by
  exact Control.GuardInstructionWindow.pc 4
@[simp] theorem pc_4102 : Control.Artifact.submissionArtifact.instructionPC 6208 = 8366 := by
  exact Control.GuardInstructionWindow.pc 5
@[simp] theorem pc_4103 : Control.Artifact.submissionArtifact.instructionPC 6209 = 8367 := by
  exact Control.GuardInstructionWindow.pc 6
@[simp] theorem pc_4104 : Control.Artifact.submissionArtifact.instructionPC 6210 = 8370 := by
  exact Control.GuardInstructionWindow.pc 7
@[simp] theorem pc_4105 : Control.Artifact.submissionArtifact.instructionPC 6211 = 8371 := by
  exact Control.GuardInstructionWindow.pc 8
@[simp] theorem pc_241 : Control.Artifact.submissionArtifact.instructionPC 6212 = 8392 := by
  exact Control.GuardInstructionWindow.pc 9
@[simp] theorem pc_inlineStore : Control.Artifact.submissionArtifact.instructionPC 6213 = 8393 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineMsize : Control.Artifact.submissionArtifact.instructionPC 6214 = 8394 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineZero : Control.Artifact.submissionArtifact.instructionPC 6215 = 8395 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineReturn : Control.Artifact.submissionArtifact.instructionPC 6216 = 8396 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyDest : Control.Artifact.submissionArtifact.instructionPC 6083 = 8051 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyPush : Control.Artifact.submissionArtifact.instructionPC 6084 = 8052 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyZero0 : Control.Artifact.submissionArtifact.instructionPC 6085 = 8073 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyStore : Control.Artifact.submissionArtifact.instructionPC 6086 = 8074 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyMsize : Control.Artifact.submissionArtifact.instructionPC 6087 = 8075 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyZero1 : Control.Artifact.submissionArtifact.instructionPC 6088 = 8076 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyReturn : Control.Artifact.submissionArtifact.instructionPC 6089 = 8077 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def wordMaskNat : Nat :=
  5506022574726681700290820341793915503137370776112178186780075461015395893248

def wordMask : UInt256 := UInt256.ofNat wordMaskNat

def entryDest : Located :=
  ⟨6096, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩

def wordPath : List Located :=
    [⟨6203, .push ⟨32, by decide⟩ wordMask, by exact Control.GuardInstructionWindow.get 0, by decide⟩,
     ⟨6204, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact Control.GuardInstructionWindow.get 1, by decide⟩,
     ⟨6205, .op .CALLDATALOAD, by exact Control.GuardInstructionWindow.get 2, ⟨by decide, trivial, rfl⟩⟩,
     ⟨6206, .op .CALLDATASIZE, by exact Control.GuardInstructionWindow.get 3, ⟨by decide, trivial, rfl⟩⟩,
     ⟨6207, .op .SAR, by exact Control.GuardInstructionWindow.get 4, ⟨by decide, trivial, rfl⟩⟩,
     ⟨6208, .op .XOR, by exact Control.GuardInstructionWindow.get 5, ⟨by decide, trivial, rfl⟩⟩,
     ⟨6209, .push ⟨2, by decide⟩ (UInt256.ofNat 8085), by exact Control.GuardInstructionWindow.get 6, by decide⟩,
     ⟨6210, .op .JUMPI, by exact Control.GuardInstructionWindow.get 7, ⟨by decide, trivial, rfl⟩⟩]

def wordMissPath : List Located := wordPath ++ [entryDest]

def storePath : List Located :=
  [⟨6211, .push ⟨20, by decide⟩ (UInt256.ofNat 814647003348588794217809277549781461204094028796), by exact Control.GuardInstructionWindow.get 8, by decide⟩,
   ⟨6212, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨6213, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨6215, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨6216, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def emptyStorePath : List Located :=
  [⟨6083, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨6084, .push ⟨20, by decide⟩ (UInt256.ofNat 890993315260586290631548281360202943075753233713), by rfl, by decide⟩,
   ⟨6085, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨6086, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def emptyFinishPath : List Located :=
  [⟨6088, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨6089, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.AbcArm
