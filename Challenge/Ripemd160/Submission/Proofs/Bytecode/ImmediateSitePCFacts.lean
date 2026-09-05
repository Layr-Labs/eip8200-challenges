import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup16

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSitePCFacts

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup16

theorem leftNextPCChunk1 (i : Fin 16) :
    (leftData (16 + i.val)).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (leftData (16 + i.val + 1)).site.startIndex) := by
  fin_cases i <;> decide

theorem leftNextPCChunk2 (i : Fin 16) :
    (leftData (32 + i.val)).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (leftData (32 + i.val + 1)).site.startIndex) := by
  fin_cases i <;> decide

theorem leftNextPCChunk3 (i : Fin 16) :
    (leftData (48 + i.val)).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (leftData (48 + i.val + 1)).site.startIndex) := by
  fin_cases i <;> decide

theorem leftNextPCChunk4 (i : Fin 16) :
    (leftData (64 + i.val)).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (if i.val = 15 then (rightData 0).site.startIndex
        else (leftData (64 + i.val + 1)).site.startIndex)) := by
  fin_cases i <;> decide

theorem leftNextPC79 (i : Nat) (hi : i < 79) :
    (leftData i).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (leftData (i + 1)).site.startIndex) := by
  by_cases h0 : i < 16
  · let j : Fin 16 := ⟨i, h0⟩
    simpa [j] using leftNextPC16 j
  · by_cases h1 : i < 32
    · let j : Fin 16 := ⟨i - 16, by omega⟩
      have hj : 16 + j.val = i := by
        dsimp [j]
        omega
      simpa [hj] using leftNextPCChunk1 j
    · by_cases h2 : i < 48
      · let j : Fin 16 := ⟨i - 32, by omega⟩
        have hj : 32 + j.val = i := by
          dsimp [j]
          omega
        simpa [hj] using leftNextPCChunk2 j
      · by_cases h3 : i < 64
        · let j : Fin 16 := ⟨i - 48, by omega⟩
          have hj : 48 + j.val = i := by
            dsimp [j]
            omega
          simpa [hj] using leftNextPCChunk3 j
        · let j : Fin 16 := ⟨i - 64, by omega⟩
          have hj : 64 + j.val = i := by
            dsimp [j]
            omega
          have hjlast : j.val ≠ 15 := by
            dsimp [j]
            omega
          simpa [hj, hjlast] using leftNextPCChunk4 j

theorem leftLastNextPC :
    (leftData 79).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (rightData 0).site.startIndex) := by
  simpa using leftNextPCChunk4 (15 : Fin 16)

theorem leftSite80_start : (leftSite 80).startIndex = 1717 := by
  decide

theorem rightNextPCChunk0 (i : Fin 16) :
    (rightData i.val).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (1717 + 9 * (i.val + 1))) := by
  fin_cases i <;> decide

theorem rightNextPCChunk1 (i : Fin 16) :
    (rightData (16 + i.val)).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (1717 + 9 * (16 + i.val + 1))) := by
  fin_cases i <;> decide

theorem rightNextPCChunk2 (i : Fin 16) :
    (rightData (32 + i.val)).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (1717 + 9 * (32 + i.val + 1))) := by
  fin_cases i <;> decide

theorem rightNextPCChunk3 (i : Fin 16) :
    (rightData (48 + i.val)).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (1717 + 9 * (48 + i.val + 1))) := by
  fin_cases i <;> decide

theorem rightNextPCChunk4 (i : Fin 15) :
    (rightData (64 + i.val)).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (1717 + 9 * (64 + i.val + 1))) := by
  fin_cases i <;> decide

theorem rightNextPC79 (i : Nat) (hi : i < 79) :
    (rightData i).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (1717 + 9 * (i + 1))) := by
  by_cases h0 : i < 16
  · let j : Fin 16 := ⟨i, h0⟩
    simpa [j] using rightNextPCChunk0 j
  · by_cases h1 : i < 32
    · let j : Fin 16 := ⟨i - 16, by omega⟩
      have hj : 16 + j.val = i := by
        dsimp [j]
        omega
      simpa [hj] using rightNextPCChunk1 j
    · by_cases h2 : i < 48
      · let j : Fin 16 := ⟨i - 32, by omega⟩
        have hj : 32 + j.val = i := by
          dsimp [j]
          omega
        simpa [hj] using rightNextPCChunk2 j
      · by_cases h3 : i < 64
        · let j : Fin 16 := ⟨i - 48, by omega⟩
          have hj : 48 + j.val = i := by
            dsimp [j]
            omega
          simpa [hj] using rightNextPCChunk3 j
        · let j : Fin 15 := ⟨i - 64, by omega⟩
          have hj : 64 + j.val = i := by
            dsimp [j]
            omega
          simpa [hj] using rightNextPCChunk4 j

theorem leftNextPC_fin80 (i : Fin 80) :
    (leftSite i.val).ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (leftSite (i.val + 1)).startIndex) := by
  by_cases h : i.val < 79
  · simpa [leftData] using leftNextPC79 i.val h
  · have hi : i.val = 79 := by omega
    have hi' : i = (79 : Fin 80) := Fin.ext hi
    rw [hi']
    decide

theorem rightNextPC_fin79 (i : Fin 79) :
    (rightData i.val).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (1717 + 9 * (i.val + 1))) := by
  exact rightNextPC79 i.val i.isLt

theorem rightNextPC78 :
    (rightData 78).site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2428) := by
  decide

theorem right78_returnIndex : (rightData 78).returnIndex = 2427 := by
  rfl

theorem right78_extraPush0 :
    Artifact.submissionArtifact.instructions[2428]? =
      some (.push ⟨0, by decide⟩ (UInt256.ofNat 0)) := by
  rfl

theorem rightFinal_returnIndex : (rightData 79).returnIndex = 563 := by
  rfl

theorem rightFinal_returnPC : (rightData 79).returnPC = 804 := by
  decide

theorem rightFinal_returnDest :
    (rightData 79).site.ret = UInt256.ofNat 0x324 := by
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSitePCFacts
