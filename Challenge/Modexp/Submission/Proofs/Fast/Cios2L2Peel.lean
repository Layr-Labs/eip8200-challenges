import Challenge.Modexp.Submission.Proofs.Fast.Cios2Mid
import Challenge.Modexp.Submission.Proofs.Fast.MacAlt
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # CIOS2 peeled L2 MAC -/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Peel

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Mid
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel

set_option linter.unusedSimpArgs false in
theorem run_peel (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hn : 2 < n) :
    Challenge.EvmProof.Stepper.runLocatedBlock cios2L2Peel
      (l2At 4776 s mid bi mu c0 pa pb n i 0 pdst ret rest) =
      some (l2At 4913 s mid bi mu c0 pa pb n i 1 pdst ret rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hK :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have hpmj : ptrAt (32 * n - 64) 0 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * (n - 2) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hptj : ptrAt (8192 + 32 * n) 0 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 2) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hwr : ptrAt (8224 + 32 * n) 0 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpm0 : (32 * n - 64) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * (n - 2) := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hpt0 : (8192 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 2) := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hwr0 : (32 + (8192 + 32 * n)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1) := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hwr1 : (8192 + 32 * n + 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1) := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hnextM :
      115792089237316195423570985008687907853269984665640564039457584007913129639904 +
          (32 * n - 64) = ptrAt (32 * n - 64) 1 := by
    simpa using ptrAt_succ (32 * n - 64) 0
  have hnextT :
      115792089237316195423570985008687907853269984665640564039457584007913129639904 +
          (8192 + 32 * n) = ptrAt (8192 + 32 * n) 1 := by
    simpa using ptrAt_succ (8192 + 32 * n) 0
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 2)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 2)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [cios2L2Peel, Cios2Paths.L2Peel.peelPC, Cios2Paths.L2Peel.peelStartIndex,
      Cios2Paths.L2Peel.peelOpAt, Cios2Paths.L2Peel.peelPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l2At, l2Step, macSum, macCarry, mulHi, maxWord_literal,
      fastPC13, fastPC14,
      hc10, hc11, hc12, hc13, hc14, hrun, hK, h32, h8224,
      hpmj, hptj, hwr, hpm0, hpt0, hwr0, hwr1, hnextM, hnextT,
      hactM, hactT, hactW, ptrAt_succ, ptrAt_shift32,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩
  rw [MacAlt.macSumNat]

def gasSteps_peel (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hn : 2 < n) :
    Challenge.EvmProof.GasSteps
      (l2At 4776 s mid bi mu c0 pa pb n i 0 pdst ret rest)
      (l2At 4913 s mid bi mu c0 pa pb n i 1 pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka cios2L2Peel hcode hfork
    (run_peel s mid bi mu c0 pa pb n i pdst ret rest hcap hrun hact hn32 hn)
      hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Peel
