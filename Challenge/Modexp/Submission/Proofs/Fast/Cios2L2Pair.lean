import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Peel
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
import Challenge.Modexp.Submission.Proofs.Fast.MacAlt

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # CIOS2 paired L2 MACs -/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Mid
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

def tailState (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 5195
           stack := [pmj, ptj, c, mu, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := mem }

theorem jumpDest4913 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4913 = true := by
  exact Artifact.isValidJumpDest_index 2970 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_first (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k + 2 < n) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstMac
      (l2At 4913 s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (l2At 5050 s mid bi mu c0 pa pb n i (k + 1) pdst ret rest) := by
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
    [firstMac, Cios2Paths.L2Pair.firstPC, Cios2Paths.L2Pair.firstStartIndex,
      Cios2Paths.L2Pair.firstOpAt, Cios2Paths.L2Pair.firstPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l2At, l2Step, macSum, macCarry, mulHi, maxWord_literal,
      fastPC13, fastPC14,
      hc10, hc11, hc12, hc13, hc14, hrun, hK, h32, h8224,
      hpmj, hptj, hwr, hwr1, hactM, hactT, hactW, ptrAt_succ, ptrAt_shift32,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩
  rw [MacAlt.macSumNat]

set_option linter.unusedSimpArgs false in
theorem run_secondBody (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k + 2 < n) :
    Challenge.EvmProof.Stepper.runLocatedBlock secondMac
      (l2At 5050 s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (l2At 4913 s mid bi mu c0 pa pb n i (k + 1) pdst ret rest) := by
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
  have h4938 : (4913 : UInt256).toNat = 4913 := by decide
  have h4938' : (4913 : UInt256) = UInt256.ofNat 4913 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (4913 : UInt256).toNat = true := by
    rw [h4938]
    exact jumpDest4913
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
  have hnextT : ptrAt (8192 + 32 * n) (k + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8160 + 32 * n - 32 * k := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hgt : 8224 < 8160 + 32 * n - 32 * k := by omega
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
    [secondMac, Cios2Paths.L2Pair.secondPC, Cios2Paths.L2Pair.secondStartIndex,
      Cios2Paths.L2Pair.secondOpAt, Cios2Paths.L2Pair.secondPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l2At, l2Step, macSum, macCarry, mulHi, maxWord_literal,
      fastPC13, fastPC14,
      hc10, hc11, hc12, hc13, hc14, hrun, hcode, hK, h32, h8224,
      h4938, h4938', hjump, jumpDest4913,
      hpmj, hptj, hwr, hwr1, hnextT, hgt, hactM, hactT, hactW,
      ptrAt_succ, ptrAt_shift32, UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩
  rw [MacAlt.macSumNat]

set_option linter.unusedSimpArgs false in
theorem run_secondExit (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k + 2 = n) :
    Challenge.EvmProof.Stepper.runLocatedBlock secondMac
      (l2At 5050 s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (tailState s (l2Step mid mu c0 n (k + 1)).memory
        (UInt256.ofNat (ptrAt (32 * n - 64) (k + 1)))
        (UInt256.ofNat (ptrAt (8192 + 32 * n) (k + 1)))
        (l2Step mid mu c0 n (k + 1)).carry mu bi pa pb n i pdst ret rest) := by
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
  have hnextT : ptrAt (8192 + 32 * n) (k + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224 := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
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
    [secondMac, Cios2Paths.L2Pair.secondPC, Cios2Paths.L2Pair.secondStartIndex,
      Cios2Paths.L2Pair.secondOpAt, Cios2Paths.L2Pair.secondPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l2At, tailState, l2Step, macSum, macCarry, mulHi, maxWord_literal,
      fastPC13, fastPC14,
      hc10, hc11, hc12, hc13, hc14, hrun, hK, h32, h8224,
      hpmj, hptj, hwr, hwr1, hnextT, hactM, hactT, hactW,
      ptrAt_succ, ptrAt_shift32, UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩
  rw [MacAlt.macSumNat]

def gasSteps_first (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 2 < n) :
    Challenge.EvmProof.GasSteps
      (l2At 4913 s mid bi mu c0 pa pb n i k pdst ret rest)
      (l2At 5050 s mid bi mu c0 pa pb n i (k + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka firstMac hcode hfork
    (run_first s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun hact hn32 hk)
      hrun hnp

def gasSteps_secondBody (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 2 < n) :
    Challenge.EvmProof.GasSteps
      (l2At 5050 s mid bi mu c0 pa pb n i k pdst ret rest)
      (l2At 4913 s mid bi mu c0 pa pb n i (k + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka secondMac hcode hfork
    (run_secondBody s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun hcode hact hn32 hk)
      hrun hnp

def gasSteps_secondExit (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 2 = n) :
    Challenge.EvmProof.GasSteps
      (l2At 5050 s mid bi mu c0 pa pb n i k pdst ret rest)
      (tailState s (l2Step mid mu c0 n (k + 1)).memory
        (UInt256.ofNat (ptrAt (32 * n - 64) (k + 1)))
        (UInt256.ofNat (ptrAt (8192 + 32 * n) (k + 1)))
        (l2Step mid mu c0 n (k + 1)).carry mu bi pa pb n i pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka secondMac hcode hfork
    (run_secondExit s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun hact hn32 hk)
      hrun hnp

def gasSteps_pairBody (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 3 < n) :
    Challenge.EvmProof.GasSteps
      (l2At 4913 s mid bi mu c0 pa pb n i k pdst ret rest)
      (l2At 4913 s mid bi mu c0 pa pb n i (k + 2) pdst ret rest) :=
  (gasSteps_first s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 (by omega)).trans
    (gasSteps_secondBody s mid bi mu c0 pa pb n i (k + 1) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega))

def gasSteps_pairExit (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 3 = n) :
    Challenge.EvmProof.GasSteps
      (l2At 4913 s mid bi mu c0 pa pb n i k pdst ret rest)
      (tailState s (l2Step mid mu c0 n (k + 2)).memory
        (UInt256.ofNat (ptrAt (32 * n - 64) (k + 2)))
        (UInt256.ofNat (ptrAt (8192 + 32 * n) (k + 2)))
        (l2Step mid mu c0 n (k + 2)).carry mu bi pa pb n i pdst ret rest) :=
  (gasSteps_first s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 (by omega)).trans
    (gasSteps_secondExit s mid bi mu c0 pa pb n i (k + 1) pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 (by omega))

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair
