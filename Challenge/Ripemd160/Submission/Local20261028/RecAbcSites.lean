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

@[simp] theorem pc_176 : Control.Artifact.submissionArtifact.instructionPC 3356 = 4658 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4095 : Control.Artifact.submissionArtifact.instructionPC 3431 = 4840 := by
  exact Control.GuardInstructionWindow.pc 0
@[simp] theorem pc_4096 : Control.Artifact.submissionArtifact.instructionPC 3434 = 4847 := by
  exact Control.GuardInstructionWindow.pc 3
@[simp] theorem pc_4097 : Control.Artifact.submissionArtifact.instructionPC 3435 = 4848 := by
  exact Control.GuardInstructionWindow.pc 4
@[simp] theorem pc_4098 : Control.Artifact.submissionArtifact.instructionPC 3436 = 4849 := by
  exact Control.GuardInstructionWindow.pc 5
@[simp] theorem pc_4101 : Control.Artifact.submissionArtifact.instructionPC 3437 = 4850 := by
  exact Control.GuardInstructionWindow.pc 6
@[simp] theorem pc_4102 : Control.Artifact.submissionArtifact.instructionPC 3438 = 4851 := by
  exact Control.GuardInstructionWindow.pc 7
@[simp] theorem pc_4103 : Control.Artifact.submissionArtifact.instructionPC 3439 = 4852 := by
  exact Control.GuardInstructionWindow.pc 8
@[simp] theorem pc_4104 : Control.Artifact.submissionArtifact.instructionPC 3440 = 4855 := by
  exact Control.GuardInstructionWindow.pc 9
@[simp] theorem pc_4105 : Control.Artifact.submissionArtifact.instructionPC 3441 = 4856 := by
  exact Control.GuardInstructionWindow.pc 10
@[simp] theorem pc_241 : Control.Artifact.submissionArtifact.instructionPC 3442 = 4877 := by
  exact Control.GuardInstructionWindow.pc 11
@[simp] theorem pc_inlineStore : Control.Artifact.submissionArtifact.instructionPC 3443 = 4878 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineMsize : Control.Artifact.submissionArtifact.instructionPC 3444 = 4879 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineZero : Control.Artifact.submissionArtifact.instructionPC 3445 = 4880 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineReturn : Control.Artifact.submissionArtifact.instructionPC 3446 = 4881 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyDest : Control.Artifact.submissionArtifact.instructionPC 3343 = 4624 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyPush : Control.Artifact.submissionArtifact.instructionPC 3344 = 4625 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyZero0 : Control.Artifact.submissionArtifact.instructionPC 3345 = 4646 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyStore : Control.Artifact.submissionArtifact.instructionPC 3346 = 4647 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyMsize : Control.Artifact.submissionArtifact.instructionPC 3347 = 4648 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyZero1 : Control.Artifact.submissionArtifact.instructionPC 3348 = 4649 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyReturn : Control.Artifact.submissionArtifact.instructionPC 3349 = 4650 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def wordMaskNat : Nat :=
  5506022574726681700290820341793915503137370776112178186780075461015395893248

def wordMask : UInt256 := UInt256.ofNat wordMaskNat

def entryDest : Located :=
  ⟨3356, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩

def wordPath : List Located :=
    [⟨3431, .push ⟨3, by decide⟩ (UInt256.ofNat 6382179), by exact Control.GuardInstructionWindow.get 0, by decide⟩,
     ⟨3432, .push ⟨1, by decide⟩ (UInt256.ofNat 229), by exact Control.GuardInstructionWindow.get 1, by decide⟩,
     ⟨3433, .op .SHL, by exact Control.GuardInstructionWindow.get 2, ⟨by decide, trivial, rfl⟩⟩,
     ⟨3434, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact Control.GuardInstructionWindow.get 3, by decide⟩,
     ⟨3435, .op .CALLDATALOAD, by exact Control.GuardInstructionWindow.get 4, ⟨by decide, trivial, rfl⟩⟩,
     ⟨3436, .op .CALLDATASIZE, by exact Control.GuardInstructionWindow.get 5, ⟨by decide, trivial, rfl⟩⟩,
     ⟨3437, .op .SAR, by exact Control.GuardInstructionWindow.get 6, ⟨by decide, trivial, rfl⟩⟩,
     ⟨3438, .op .XOR, by exact Control.GuardInstructionWindow.get 7, ⟨by decide, trivial, rfl⟩⟩,
     ⟨3439, .push ⟨2, by decide⟩ (UInt256.ofNat 4658), by exact Control.GuardInstructionWindow.get 8, by decide⟩,
     ⟨3440, .op .JUMPI, by exact Control.GuardInstructionWindow.get 9, ⟨by decide, trivial, rfl⟩⟩]

def wordMissPath : List Located := wordPath ++ [entryDest]

def storePath : List Located :=
  [⟨3441, .push ⟨20, by decide⟩ (UInt256.ofNat 814647003348588794217809277549781461204094028796), by exact Control.GuardInstructionWindow.get 10, by decide⟩,
   ⟨3442, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨3443, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨3445, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨3446, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def emptyStorePath : List Located :=
  [⟨3343, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3344, .push ⟨20, by decide⟩ (UInt256.ofNat 890993315260586290631548281360202943075753233713), by rfl, by decide⟩,
   ⟨3345, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨3346, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def emptyFinishPath : List Located :=
  [⟨3348, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨3349, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.AbcArm
