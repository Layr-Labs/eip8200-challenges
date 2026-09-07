import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Core

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_l1FourthMacExit (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k + 1 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock fourthMac
      (l1At 4551 s mem bi pa pb n i k pdst ret rest) =
      some (midState s (l1Step mem bi pa n (k + 1)).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) (k + 1)))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) (k + 1)))
        (l1Step mem bi pa n (k + 1)).carry bi pa pb n i pdst ret rest) := by
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
  have hpaj : ptrAt (pa + 32 * n - 32) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hptj : ptrAt (8224 + 32 * n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hnextA : ptrAt (pa + 32 * n - 32) (k + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpamN : (pa - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [fourthMac, Cios2Paths.L1.fourthPC, Cios2Paths.L1.fourthStartIndex,
      Cios2Paths.L1.fourthOpAt, Cios2Paths.L1.fourthPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l1At, midState, l1Step, macSum, macCarry, mulHi, maxWord_literal,
      hc9, hc10, hc11, hc12, hc13, hrun, hK,
      hpaj, hptj, hnextA, hpamN, hactA, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

def gasSteps_l1FourthMacExit (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 1 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4551 s mem bi pa pb n i k pdst ret rest)
      (midState s (l1Step mem bi pa n (k + 1)).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) (k + 1)))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) (k + 1)))
        (l1Step mem bi pa n (k + 1)).carry bi pa pb n i pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka fourthMac hcode hfork
    (run_l1FourthMacExit s mem bi pa pb n i k pdst ret rest hcap hrun hact hn32
      hk hpa hpaFit) hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac
