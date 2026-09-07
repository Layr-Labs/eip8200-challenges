import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac
import Challenge.Modexp.Submission.Proofs.Fast.MacAlt

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # No-test middle copies of the four-way CIOS2 L1 block -/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Middle

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_l1MiddleOneMac (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j + 1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock middleOneMac
      (l1At 4270 s mem bi pa pb n i j pdst ret rest) =
      some (l1At 4403 s mem bi pa pb n i (j + 1) pdst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hK :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have hpaj : ptrAt (pa + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hptj : ptrAt (8224 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hnextA : ptrAt (pa + 32 * n - 32) (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 2 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpamN : (pa - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hgt : pa - 32 < pa + 32 * (n - 2 - j) := by omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [middleOneMac, Cios2Paths.L1.middleOnePC, Cios2Paths.L1.middleOneStartIndex,
      Cios2Paths.L1.middleOneOpAt, Cios2Paths.L1.middleOnePushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l1At, l1Step, macSum, macCarry, mulHi, maxWord_literal,
      hc9, hc10, hc11, hc12, hc13, hrun, hcode, hK,
      hpaj, hptj, hnextA, hpamN, hgt, hactA, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩
  rw [MacAlt.macSumNat]

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_l1MiddleTwoMac (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j + 1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock middleTwoMac
      (l1At 4403 s mem bi pa pb n i j pdst ret rest) =
      some (l1At 4536 s mem bi pa pb n i (j + 1) pdst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hK :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have hpaj : ptrAt (pa + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hptj : ptrAt (8224 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hnextA : ptrAt (pa + 32 * n - 32) (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 2 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpamN : (pa - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hgt : pa - 32 < pa + 32 * (n - 2 - j) := by omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [middleTwoMac, Cios2Paths.L1.middleTwoPC, Cios2Paths.L1.middleTwoStartIndex,
      Cios2Paths.L1.middleTwoOpAt, Cios2Paths.L1.middleTwoPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l1At, l1Step, macSum, macCarry, mulHi, maxWord_literal,
      hc9, hc10, hc11, hc12, hc13, hrun, hcode, hK,
      hpaj, hptj, hnextA, hpamN, hgt, hactA, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩
  rw [MacAlt.macSumNat]

def gasSteps_l1MiddleOneMac (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hj : j + 1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4270 s mem bi pa pb n i j pdst ret rest)
      (l1At 4403 s mem bi pa pb n i (j + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka middleOneMac hcode hfork
    (run_l1MiddleOneMac s mem bi pa pb n i j pdst ret rest hcap hrun hcode hact
      hn32 hj hpa hpaFit) hrun hnp

def gasSteps_l1MiddleTwoMac (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hj : j + 1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4403 s mem bi pa pb n i j pdst ret rest)
      (l1At 4536 s mem bi pa pb n i (j + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka middleTwoMac hcode hfork
    (run_l1MiddleTwoMac s mem bi pa pb n i j pdst ret rest hcap hrun hcode hact
      hn32 hj hpa hpaFit) hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Middle
