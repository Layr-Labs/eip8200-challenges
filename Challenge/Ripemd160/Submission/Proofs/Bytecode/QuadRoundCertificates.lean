import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRawTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# Q4M quad-round certificates

Each certificate composes one ten-push call, one quad helper, and one return
jump, and identifies the result with four `StackCompression` steps.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

abbrev Artifact := QuadSites.Artifact

private theorem leftIndex_lt (i : Fin 80) :
    Crypto.Ripemd160.r[i.val]! < 16 := by
  fin_cases i <;> decide

private theorem rightIndex_lt (i : Fin 80) :
    Crypto.Ripemd160.rP[i.val]! < 16 := by
  fin_cases i <;> decide

theorem leftAddress_toNat (i : Fin 80) :
    (StackRoundData.leftAddress i.val).toNat =
      644 + 4 * Crypto.Ripemd160.r[i.val]! := by
  have hi := leftIndex_lt i
  unfold StackRoundData.leftAddress
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem rightAddress_toNat (i : Fin 80) :
    (StackRoundData.rightAddress i.val).toNat =
      644 + 4 * Crypto.Ripemd160.rP[i.val]! := by
  have hi := rightIndex_lt i
  unfold StackRoundData.rightAddress
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem leftAddress_bound (i : Fin 80) :
    (StackRoundData.leftAddress i.val).toNat + 32 ≤ 2144 := by
  rw [leftAddress_toNat]
  have := leftIndex_lt i
  omega

theorem rightAddress_bound (i : Fin 80) :
    (StackRoundData.rightAddress i.val).toNat + 32 ≤ 2144 := by
  rw [rightAddress_toNat]
  have := rightIndex_lt i
  omega

private theorem leftWord (s : State) (word : Nat → UInt32) (i : Fin 80)
    (hwords : ∀ n, n < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * n)) = word n) :
    Word.toUInt32 (MachineState.readWord s.memory
      (StackRoundData.leftAddress i.val).toNat) =
      word (Crypto.Ripemd160.r[i.val]!) := by
  rw [leftAddress_toNat i]
  exact hwords _ (leftIndex_lt i)

private theorem rightWord (s : State) (word : Nat → UInt32) (i : Fin 80)
    (hwords : ∀ n, n < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * n)) = word n) :
    Word.toUInt32 (MachineState.readWord s.memory
      (StackRoundData.rightAddress i.val).toNat) =
      word (Crypto.Ripemd160.rP[i.val]!) := by
  rw [rightAddress_toNat i]
  exact hwords _ (rightIndex_lt i)

def pureQuadWorking (s : State) (working : EvmWorking) (j : Nat)
    (p0 p1 p2 p3 M0 M1 M2 M3 constant : UInt256) : EvmWorking :=
  QuadRoundState.quadWorking s working j p0 p1 p2 p3 M0 M1 M2 M3 constant

private theorem leftConstant_zero (k : Fin 20) (hzero : k.val / 4 = 0) :
    QuadSites.leftConstant k = 0 := by
  fin_cases k <;>
    simp_all [QuadSites.leftConstant, StackRoundData.leftConstant] <;>
    decide

private theorem rightConstant_zero (k : Fin 20) (hzero : 4 - k.val / 4 = 0) :
    QuadSites.rightConstant k = 0 := by
  fin_cases k <;>
    simp_all [QuadSites.rightConstant, StackRoundData.rightConstant] <;>
    decide

theorem pureQuadWorking_left (s : State) (word : Nat → UInt32)
    (working : EvmWorking) (k : Fin 20)
    (hwords : ∀ n, n < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * n)) = word n) :
    pureQuadWorking s working (k.val / 4)
        (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
        (leftM0 k) (leftM1 k) (leftM2 k) (leftM3 k) (QuadSites.leftConstant k) =
      StackCompression.leftStep word (4 * k.val + 3)
        (StackCompression.leftStep word (4 * k.val + 2)
          (StackCompression.leftStep word (4 * k.val + 1)
            (StackCompression.leftStep word (4 * k.val) working))) := by
  unfold pureQuadWorking leftM0 leftM1 leftM2 leftM3
  rw [QuadRoundModel.quadWorking_eq_rawRounds s working (k.val / 4)
    (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
    (leftRotation0 k) (leftRotation1 k) (leftRotation2 k) (leftRotation3 k)
    (QuadSites.leftConstant k) (by omega) (leftRotation0_le32 k) (leftRotation1_le32 k)
    (leftRotation2_le32 k) (leftRotation3_le32 k) (fun h => leftConstant_zero k h)]
  rw [QuadRoundModel.fourRawRound_eq_of_toUInt32_eq working (k.val / 4)
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.r[4 * k.val]!)))
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.r[4 * k.val + 1]!)))
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.r[4 * k.val + 2]!)))
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.r[4 * k.val + 3]!)))
    _ _ _ _ _
    (by simpa only [Word.toUInt32_ofUInt32, leftAddress0] using leftWord s word ⟨4 * k.val, by omega⟩ hwords)
    (by simpa only [Word.toUInt32_ofUInt32, leftAddress1] using
      leftWord s word ⟨4 * k.val + 1, by omega⟩ hwords)
    (by simpa only [Word.toUInt32_ofUInt32, leftAddress2] using
      leftWord s word ⟨4 * k.val + 2, by omega⟩ hwords)
    (by simpa only [Word.toUInt32_ofUInt32, leftAddress3] using
      leftWord s word ⟨4 * k.val + 3, by omega⟩ hwords)]
  fin_cases k <;> rfl

theorem pureQuadWorking_right (s : State) (word : Nat → UInt32)
    (working : EvmWorking) (k : Fin 20)
    (hwords : ∀ n, n < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * n)) = word n) :
    pureQuadWorking s working (4 - k.val / 4)
        (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
        (rightM0 k) (rightM1 k) (rightM2 k) (rightM3 k) (QuadSites.rightConstant k) =
      StackCompression.rightStep word (4 * k.val + 3)
        (StackCompression.rightStep word (4 * k.val + 2)
          (StackCompression.rightStep word (4 * k.val + 1)
            (StackCompression.rightStep word (4 * k.val) working))) := by
  unfold pureQuadWorking rightM0 rightM1 rightM2 rightM3
  rw [QuadRoundModel.quadWorking_eq_rawRounds s working (4 - k.val / 4)
    (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
    (rightRotation0 k) (rightRotation1 k) (rightRotation2 k) (rightRotation3 k)
    (QuadSites.rightConstant k) (by omega) (rightRotation0_le32 k) (rightRotation1_le32 k)
    (rightRotation2_le32 k) (rightRotation3_le32 k) (fun h => rightConstant_zero k h)]
  rw [QuadRoundModel.fourRawRound_eq_of_toUInt32_eq working (4 - k.val / 4)
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.rP[4 * k.val]!)))
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.rP[4 * k.val + 1]!)))
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.rP[4 * k.val + 2]!)))
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.rP[4 * k.val + 3]!)))
    _ _ _ _ _
    (by simpa only [Word.toUInt32_ofUInt32, rightAddress0] using rightWord s word ⟨4 * k.val, by omega⟩ hwords)
    (by simpa only [Word.toUInt32_ofUInt32, rightAddress1] using
      rightWord s word ⟨4 * k.val + 1, by omega⟩ hwords)
    (by simpa only [Word.toUInt32_ofUInt32, rightAddress2] using
      rightWord s word ⟨4 * k.val + 2, by omega⟩ hwords)
    (by simpa only [Word.toUInt32_ofUInt32, rightAddress3] using
      rightWord s word ⟨4 * k.val + 3, by omega⟩ hwords)]
  fin_cases k <;> rfl

def gasSteps_leftQuad (s : State) (word : Nat → UInt32)
    (working : EvmWorking) (rest : List UInt256) (k : Fin 20)
    (_hwords : ∀ n, n < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * n)) = word n)
    (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s (QuadSites.leftPC k.val) working.a working.b working.c
        working.d working.e rest)
      {s with
        pc := QuadSites.leftPC (k.val + 1)
        stack := roundWords
          (pureQuadWorking s working (k.val / 4)
            (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
            (leftM0 k) (leftM1 k) (leftM2 k) (leftM3 k) (QuadSites.leftConstant k)) ++ rest} := by
  let site := QuadSites.leftRoundSite k
  have hraw :
      runInstrSeq (quadBeforeJumpTemplate (k.val / 4) (QuadSites.leftConstant k))
        (quadHelperEntry s site.helper.startPC (leftAddress0 k) (leftAddress1 k)
          (leftAddress2 k) (leftAddress3 k) site.returnPC
          (leftM0 k) (leftM1 k) (leftM2 k) (leftM3 k) working rest) =
      some (quadAfterHelperBeforeJump s
        (pcAfter site.helper.startPC (quadBeforeJumpTemplate (k.val / 4) (QuadSites.leftConstant k)))
        site.returnPC
        (quadWorking s working (k.val / 4) (leftAddress0 k) (leftAddress1 k)
          (leftAddress2 k) (leftAddress3 k)
          (leftM0 k) (leftM1 k) (leftM2 k) (leftM3 k) (QuadSites.leftConstant k)) rest) := by
    exact QuadRawTrace.runInstrSeq_template (k.val / 4) (by omega) s
      site.helper.startPC (leftAddress0 k) (leftAddress1 k) (leftAddress2 k)
      (leftAddress3 k) site.returnPC (leftM0 k) (leftM1 k) (leftM2 k) (leftM3 k)
      (QuadSites.leftConstant k) working rest hstack hrun hactive
      (leftAddress_bound ⟨4 * k.val, by omega⟩)
      (leftAddress_bound ⟨4 * k.val + 1, by omega⟩)
      (leftAddress_bound ⟨4 * k.val + 2, by omega⟩)
      (leftAddress_bound ⟨4 * k.val + 3, by omega⟩)
  have ghelper := QuadHelperTrace.gasSteps_helper_of_raw
    (j := k.val / 4) (hj := by omega)
    (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
    (leftM0 k) (leftM1 k) (leftM2 k) (leftM3 k) (QuadSites.leftConstant k)
    site.helper s site.returnPC working rest hraw hrun hcode hfork hnp
  have g := QuadHelperTrace.gasSteps_quad_of_helper
    (j := k.val / 4)
    (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
    (leftM0 k) (leftM1 k) (leftM2 k) (leftM3 k)
    (leftW0 k) (leftW1 k) (leftW2 k) (leftW3 k) (QuadSites.leftConstant k)
    site s working rest hstack hrun hcode hfork hnp ghelper
  exact g.cast
    (by rw [QuadSites.leftRoundSite_start k])
    (by rw [QuadSites.leftRoundSite_end k]; rfl)

def gasSteps_rightQuad (s : State) (word : Nat → UInt32)
    (working : EvmWorking) (rest : List UInt256) (k : Fin 20)
    (_hwords : ∀ n, n < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * n)) = word n)
    (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s (QuadSites.rightPC k.val) working.a working.b working.c
        working.d working.e rest)
      {s with
        pc := QuadSites.rightPC (k.val + 1)
        stack := roundWords
          (pureQuadWorking s working (4 - k.val / 4)
            (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
            (rightM0 k) (rightM1 k) (rightM2 k) (rightM3 k) (QuadSites.rightConstant k)) ++ rest} := by
  let site := QuadSites.rightRoundSite k
  have hraw :
      runInstrSeq (quadBeforeJumpTemplate (4 - k.val / 4) (QuadSites.rightConstant k))
        (quadHelperEntry s site.helper.startPC (rightAddress0 k) (rightAddress1 k)
          (rightAddress2 k) (rightAddress3 k) site.returnPC
          (rightM0 k) (rightM1 k) (rightM2 k) (rightM3 k) working rest) =
      some (quadAfterHelperBeforeJump s
        (pcAfter site.helper.startPC
          (quadBeforeJumpTemplate (4 - k.val / 4) (QuadSites.rightConstant k)))
        site.returnPC
        (quadWorking s working (4 - k.val / 4) (rightAddress0 k) (rightAddress1 k)
          (rightAddress2 k) (rightAddress3 k)
          (rightM0 k) (rightM1 k) (rightM2 k) (rightM3 k) (QuadSites.rightConstant k)) rest) := by
    exact QuadRawTrace.runInstrSeq_template (4 - k.val / 4) (by omega) s
      site.helper.startPC (rightAddress0 k) (rightAddress1 k) (rightAddress2 k)
      (rightAddress3 k) site.returnPC (rightM0 k) (rightM1 k) (rightM2 k) (rightM3 k)
      (QuadSites.rightConstant k) working rest hstack hrun hactive
      (rightAddress_bound ⟨4 * k.val, by omega⟩)
      (rightAddress_bound ⟨4 * k.val + 1, by omega⟩)
      (rightAddress_bound ⟨4 * k.val + 2, by omega⟩)
      (rightAddress_bound ⟨4 * k.val + 3, by omega⟩)
  have ghelper := QuadHelperTrace.gasSteps_helper_of_raw
    (j := 4 - k.val / 4) (hj := by omega)
    (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
    (rightM0 k) (rightM1 k) (rightM2 k) (rightM3 k) (QuadSites.rightConstant k)
    site.helper s site.returnPC working rest hraw hrun hcode hfork hnp
  have g := QuadHelperTrace.gasSteps_quad_of_helper
    (j := 4 - k.val / 4)
    (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
    (rightM0 k) (rightM1 k) (rightM2 k) (rightM3 k)
    (rightW0 k) (rightW1 k) (rightW2 k) (rightW3 k) (QuadSites.rightConstant k)
    site s working rest hstack hrun hcode hfork hnp ghelper
  exact g.cast
    (by rw [QuadSites.rightRoundSite_start k])
    (by rw [QuadSites.rightRoundSite_end k]; rfl)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates
