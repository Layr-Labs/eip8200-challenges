import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadFallthroughSitesLeft
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadFallthroughSitesRight
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-!
# H30b four-round certificates

This module composes the generic quad raw trace with the concrete combined
artifact sites.  It contains no outer frame, schedule, tail, or correctness
theorem.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression

abbrev Artifact := QuadSites.Artifact
abbrev low32DenseWordsAt := QuadSemantic.DenseWordsAt

def stateAt (s : State) (pc : UInt256) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  roundEntry s pc working.a working.b working.c working.d working.e
    (QuadRoundTemplate.factor :: rho)

def left4 (word : Nat → UInt32) (k : Fin 20)
    (working : Compression.EvmWorking) : Compression.EvmWorking :=
  StackCompression.leftStep word (quadIndex k 3)
    (StackCompression.leftStep word (quadIndex k 2)
      (StackCompression.leftStep word (quadIndex k 1)
        (StackCompression.leftStep word (quadIndex k 0) working)))

def right4 (word : Nat → UInt32) (k : Fin 20)
    (working : Compression.EvmWorking) : Compression.EvmWorking :=
  StackCompression.rightStep word (quadIndex k 3)
    (StackCompression.rightStep word (quadIndex k 2)
      (StackCompression.rightStep word (quadIndex k 1)
        (StackCompression.rightStep word (quadIndex k 0) working)))

theorem leftAddress0_eq (k : Fin 20) :
    QuadSites.leftAddress0 k = quadLeftAddress k 0 := by
  fin_cases k <;> rfl

theorem leftAddress1_eq (k : Fin 20) :
    QuadSites.leftAddress1 k = quadLeftAddress k 1 := by
  fin_cases k <;> rfl

theorem leftAddress2_eq (k : Fin 20) :
    QuadSites.leftAddress2 k = quadLeftAddress k 2 := by
  fin_cases k <;> rfl

theorem leftAddress3_eq (k : Fin 20) :
    QuadSites.leftAddress3 k = quadLeftAddress k 3 := by
  fin_cases k <;> rfl

theorem rightAddress0_eq (k : Fin 20) :
    QuadSites.rightAddress0 k = quadRightAddress k 0 := by
  fin_cases k <;> rfl

theorem rightAddress1_eq (k : Fin 20) :
    QuadSites.rightAddress1 k = quadRightAddress k 1 := by
  fin_cases k <;> rfl

theorem rightAddress2_eq (k : Fin 20) :
    QuadSites.rightAddress2 k = quadRightAddress k 2 := by
  fin_cases k <;> rfl

theorem rightAddress3_eq (k : Fin 20) :
    QuadSites.rightAddress3 k = quadRightAddress k 3 := by
  fin_cases k <;> rfl

theorem leftRotation0_eq (k : Fin 20) :
    QuadSites.leftRotation0 k = quadLeftRotation k 0 := by
  fin_cases k <;> rfl

theorem leftRotation1_eq (k : Fin 20) :
    QuadSites.leftRotation1 k = quadLeftRotation k 1 := by
  fin_cases k <;> rfl

theorem leftRotation2_eq (k : Fin 20) :
    QuadSites.leftRotation2 k = quadLeftRotation k 2 := by
  fin_cases k <;> rfl

theorem leftRotation3_eq (k : Fin 20) :
    QuadSites.leftRotation3 k = quadLeftRotation k 3 := by
  fin_cases k <;> rfl

theorem rightRotation0_eq (k : Fin 20) :
    QuadSites.rightRotation0 k = quadRightRotation k 0 := by
  fin_cases k <;> rfl

theorem rightRotation1_eq (k : Fin 20) :
    QuadSites.rightRotation1 k = quadRightRotation k 1 := by
  fin_cases k <;> rfl

theorem rightRotation2_eq (k : Fin 20) :
    QuadSites.rightRotation2 k = quadRightRotation k 2 := by
  fin_cases k <;> rfl

theorem rightRotation3_eq (k : Fin 20) :
    QuadSites.rightRotation3 k = quadRightRotation k 3 := by
  fin_cases k <;> rfl

theorem leftConstant_eq (k : Fin 20) :
    QuadSites.leftConstant k = quadLeftConstant k := by
  fin_cases k <;> rfl

theorem rightConstant_eq (k : Fin 20) :
    QuadSites.rightConstant k = quadRightConstant k := by
  fin_cases k <;> rfl

theorem leftConstant_zero (k : Fin 20)
    (hzero : k.val / 4 = 0) : QuadSites.leftConstant k = 0 := by
  fin_cases k <;>
    simp_all [QuadSites.leftConstant, StackRoundData.leftConstant] <;>
    decide

theorem rightConstant_zero (k : Fin 20)
    (hzero : 4 - k.val / 4 = 0) : QuadSites.rightConstant k = 0 := by
  fin_cases k <;>
    simp_all [QuadSites.rightConstant, StackRoundData.rightConstant] <;>
    decide

theorem leftRotation0_le32 (k : Fin 20) :
    QuadSites.leftRotation0 k ≤ 32 := by
  rw [leftRotation0_eq k]
  exact quadLeftRotation_le_32 k 0

theorem leftRotation1_le32 (k : Fin 20) :
    QuadSites.leftRotation1 k ≤ 32 := by
  rw [leftRotation1_eq k]
  exact quadLeftRotation_le_32 k 1

theorem leftRotation2_le32 (k : Fin 20) :
    QuadSites.leftRotation2 k ≤ 32 := by
  rw [leftRotation2_eq k]
  exact quadLeftRotation_le_32 k 2

theorem leftRotation3_le32 (k : Fin 20) :
    QuadSites.leftRotation3 k ≤ 32 := by
  rw [leftRotation3_eq k]
  exact quadLeftRotation_le_32 k 3

theorem rightRotation0_le32 (k : Fin 20) :
    QuadSites.rightRotation0 k ≤ 32 := by
  rw [rightRotation0_eq k]
  exact quadRightRotation_le_32 k 0

theorem rightRotation1_le32 (k : Fin 20) :
    QuadSites.rightRotation1 k ≤ 32 := by
  rw [rightRotation1_eq k]
  exact quadRightRotation_le_32 k 1

theorem rightRotation2_le32 (k : Fin 20) :
    QuadSites.rightRotation2 k ≤ 32 := by
  rw [rightRotation2_eq k]
  exact quadRightRotation_le_32 k 2

theorem rightRotation3_le32 (k : Fin 20) :
    QuadSites.rightRotation3 k ≤ 32 := by
  rw [rightRotation3_eq k]
  exact quadRightRotation_le_32 k 3

theorem leftWorking_eq (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (k : Fin 20)
    (hwords : low32DenseWordsAt s word) :
    QuadRoundState.quadWorking s working (k.val / 4)
        (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
        (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k)
        (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
        (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k)
        (QuadSites.leftConstant k) = left4 word k working := by
  have h := QuadSemantic.quadWorking_left s word working k hwords
  rw [leftAddress0_eq k, leftAddress1_eq k, leftAddress2_eq k,
    leftAddress3_eq k, leftRotation0_eq k, leftRotation1_eq k,
    leftRotation2_eq k, leftRotation3_eq k, leftConstant_eq k]
  simpa [left4] using h

theorem rightWorking_eq (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (k : Fin 20)
    (hwords : low32DenseWordsAt s word) :
    QuadRoundState.quadWorking s working (4 - k.val / 4)
        (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
        (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k)
        (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
        (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k)
        (QuadSites.rightConstant k) = right4 word k working := by
  have h := QuadSemantic.quadWorking_right s word working k hwords
  rw [rightAddress0_eq k, rightAddress1_eq k, rightAddress2_eq k,
    rightAddress3_eq k, rightRotation0_eq k, rightRotation1_eq k,
    rightRotation2_eq k, rightRotation3_eq k, rightConstant_eq k]
  simpa [right4] using h

theorem leftActiveWords_eq (s : State) (k : Fin 20)
    (hactive : 39 ≤ s.activeWords.toNat) :
    QuadRoundState.quadActiveWordsAfterUInt256_4 s
        (QuadSites.leftAddress0 k).toNat (QuadSites.leftAddress1 k).toNat
        (QuadSites.leftAddress2 k).toNat (QuadSites.leftAddress3 k).toNat =
      s.activeWords := by
  rw [leftAddress0_eq k, leftAddress1_eq k, leftAddress2_eq k,
    leftAddress3_eq k]
  exact QuadSemantic.quadLeftActiveWords_unchanged s k hactive

theorem rightActiveWords_eq (s : State) (k : Fin 20)
    (hactive : 39 ≤ s.activeWords.toNat) :
    QuadRoundState.quadActiveWordsAfterUInt256_4 s
        (QuadSites.rightAddress0 k).toNat (QuadSites.rightAddress1 k).toNat
        (QuadSites.rightAddress2 k).toNat (QuadSites.rightAddress3 k).toNat =
      s.activeWords := by
  rw [rightAddress0_eq k, rightAddress1_eq k, rightAddress2_eq k,
    rightAddress3_eq k]
  exact QuadSemantic.quadRightActiveWords_unchanged s k hactive

def normalIndexOf (k : Fin 20) (h : k.val % 4 ≠ 3) : Fin 15 :=
  ⟨k.val - k.val / 4, by omega⟩

theorem normalFin_indexOf (k : Fin 20) (h : k.val % 4 ≠ 3) :
    QuadFallthroughSitesLeft.normalFin (normalIndexOf k h) = k := by
  apply Fin.ext
  dsimp [normalIndexOf, QuadFallthroughSitesLeft.normalFin]
  omega

def fallthroughGroupOf (k : Fin 20) : Fin 5 :=
  ⟨k.val / 4, by omega⟩

theorem fallthroughK_groupOf (k : Fin 20) (h : k.val % 4 = 3) :
    QuadFallthroughSitesLeft.fallthroughK (fallthroughGroupOf k) = k := by
  apply Fin.ext
  dsimp [fallthroughGroupOf, QuadFallthroughSitesLeft.fallthroughK]
  omega

theorem rightNormalFin_indexOf (k : Fin 20) (h : k.val % 4 ≠ 3) :
    QuadFallthroughSitesRight.normalFin (normalIndexOf k h) = k := by
  apply Fin.ext
  dsimp [normalIndexOf, QuadFallthroughSitesRight.normalFin]
  omega

theorem rightFallthroughK_groupOf (k : Fin 20)
    (h : k.val % 4 = 3) :
    QuadFallthroughSitesRight.fallthroughK (fallthroughGroupOf k) = k := by
  apply Fin.ext
  dsimp [fallthroughGroupOf, QuadFallthroughSitesRight.fallthroughK]
  omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates
