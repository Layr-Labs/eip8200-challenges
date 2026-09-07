import Challenge.Modexp.Submission.Proofs.Fast.MacAlt
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Core

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Mid
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

set_option linter.unusedSimpArgs false in
theorem run_fourth (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k + 1 < n) :
    Challenge.EvmProof.Stepper.runLocatedBlock fourthMac
      (l2At 5131 s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (l2At 5172 s mid bi mu c0 pa pb n i (k + 1) pdst ret rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hK :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have hnot : UInt256.lnot ({ val := 0 } : UInt256) = maxWord := by decide
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have hpmj : ptrAt (32 * n - 64) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * (n - 2 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hptj : ptrAt (8192 + 32 * n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 2 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hwr : ptrAt (8224 + 32 * n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hwr1 : (ptrAt (8192 + 32 * n) k + 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - k) := by
    have hb : ptrAt (8192 + 32 * n) k %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        8192 + 32 * n - 32 * k := ptrAt_mod _ _ (by omega) (by omega)
    omega
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 2 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 2 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [fourthMac, Cios2Paths.L2Pair.fourthPC, Cios2Paths.L2Pair.fourthStartIndex,
      Cios2Paths.L2Pair.fourthOpAt, Cios2Paths.L2Pair.fourthPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l2At, l2Step, macSum, macCarry, mulHi, maxWord_literal,
      fastPC13, fastPC14,
      hc10, hc11, hc12, hc13, hc14, hc15, hrun, hK, hnot, h32, h8224,
      hpmj, hptj, hwr, hwr1, hactM, hactT, hactW, ptrAt_succ, ptrAt_shift32,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩
  rw [MacAlt.macSumNat]

def gasSteps_fourth (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 1 < n) :
    Challenge.EvmProof.GasSteps
      (l2At 5131 s mid bi mu c0 pa pb n i k pdst ret rest)
      (l2At 5172 s mid bi mu c0 pa pb n i (k + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka fourthMac hcode hfork
    (run_fourth s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun hact hn32 hk)
      hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair
