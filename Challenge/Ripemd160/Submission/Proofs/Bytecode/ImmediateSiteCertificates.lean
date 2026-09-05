import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificatesLeft1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificatesLeft2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificatesLeft3
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificatesLeft4
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificatesRight0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificatesRight1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificatesRight2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificatesRight3
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificatesRight4

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificates

open Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSites

def leftCertificateChunk0 (i : Fin 16) :
    ImmediateSiteCertificate (leftData i.val) :=
  leftCertificate16 i

def leftCertificate80 (i : Fin 80) :
    ImmediateSiteCertificate (leftData i.val) := by
  by_cases h0 : i.val < 16
  · let j : Fin 16 := ⟨i.val, h0⟩
    simpa [j] using leftCertificateChunk0 j
  · by_cases h1 : i.val < 32
    · let j : Fin 16 := ⟨i.val - 16, by omega⟩
      have hj : 16 + j.val = i.val := by
        dsimp [j]
        omega
      simpa [hj] using leftCertificateChunk1 j
    · by_cases h2 : i.val < 48
      · let j : Fin 16 := ⟨i.val - 32, by omega⟩
        have hj : 32 + j.val = i.val := by
          dsimp [j]
          omega
        simpa [hj] using leftCertificateChunk2 j
      · by_cases h3 : i.val < 64
        · let j : Fin 16 := ⟨i.val - 48, by omega⟩
          have hj : 48 + j.val = i.val := by
            dsimp [j]
            omega
          simpa [hj] using leftCertificateChunk3 j
        · let j : Fin 16 := ⟨i.val - 64, by omega⟩
          have hj : 64 + j.val = i.val := by
            dsimp [j]
            omega
          simpa [hj] using leftCertificateChunk4 j

def rightCertificate80 (i : Fin 80) :
    ImmediateSiteCertificate (rightData i.val) := by
  by_cases h0 : i.val < 16
  · let j : Fin 16 := ⟨i.val, h0⟩
    simpa [j] using rightCertificateChunk0 j
  · by_cases h1 : i.val < 32
    · let j : Fin 16 := ⟨i.val - 16, by omega⟩
      have hj : 16 + j.val = i.val := by
        dsimp [j]
        omega
      simpa [hj] using rightCertificateChunk1 j
    · by_cases h2 : i.val < 48
      · let j : Fin 16 := ⟨i.val - 32, by omega⟩
        have hj : 32 + j.val = i.val := by
          dsimp [j]
          omega
        simpa [hj] using rightCertificateChunk2 j
      · by_cases h3 : i.val < 64
        · let j : Fin 16 := ⟨i.val - 48, by omega⟩
          have hj : 48 + j.val = i.val := by
            dsimp [j]
            omega
          simpa [hj] using rightCertificateChunk3 j
        · let j : Fin 16 := ⟨i.val - 64, by omega⟩
          have hj : 64 + j.val = i.val := by
            dsimp [j]
            omega
          simpa [hj] using rightCertificateChunk4 j

def rightCertificate79 (i : Fin 79) :
    ImmediateSiteCertificate (rightData i.val) :=
  rightCertificate80 ⟨i.val, by omega⟩

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificates
