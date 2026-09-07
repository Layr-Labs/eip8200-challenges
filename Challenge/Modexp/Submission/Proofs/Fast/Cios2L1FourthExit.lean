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

theorem jumpDest4731 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4731 = true := by
  exact Artifact.isValidJumpDest_index 3031 (by rfl)

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_selectContinue (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hn32 : n ≤ 32) (hj : j < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectBlock
      (l1At 4448 s mem bi pa pb n i j pdst ret rest) = some (l1At 4455 s mem bi pa pb n i j pdst ret rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hdest : (4731 : UInt256).toNat = 4731 := by decide
  have hdest' : (4731 : UInt256) = UInt256.ofNat 4731 := by decide
  have hpaj : ptrAt (pa + 32 * n - 32) j % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpam : (pa - 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hne : pa + 32 * (n - 1 - j) ≠ pa - 32 := by omega
  simp (config := { maxSteps := 800000 })
    [selectBlock, Cios2Paths.L1.selectPC, Cios2Paths.L1.selectStartIndex,
      Cios2Paths.L1.selectOpAt, Cios2Paths.L1.selectPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l1At, hc10, hc11, hc12, hc13, hrun, hcode, hdest, hdest',
      jumpDest4731, hpaj, hpam, hne, UInt256.eq, UInt256.isTrue,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

def gasSteps_selectContinue (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hn32 : n ≤ 32) (hj : j < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (l1At 4448 s mem bi pa pb n i j pdst ret rest) (l1At 4455 s mem bi pa pb n i j pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectBlock hcode hfork
    (run_selectContinue s mem bi pa pb n i j pdst ret rest hcap hrun hcode hn32 hj hpa hpaFit) hrun hnp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_selectExit (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hn32 : n ≤ 32) (hj : j = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectBlock
      (l1At 4448 s mem bi pa pb n i j pdst ret rest) = some (l1At 4731 s mem bi pa pb n i j pdst ret rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hdest : (4731 : UInt256).toNat = 4731 := by decide
  have hdest' : (4731 : UInt256) = UInt256.ofNat 4731 := by decide
  have hpaj : ptrAt (pa + 32 * n - 32) j % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpam : (pa - 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa - 32 := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 800000 })
    [selectBlock, Cios2Paths.L1.selectPC, Cios2Paths.L1.selectStartIndex,
      Cios2Paths.L1.selectOpAt, Cios2Paths.L1.selectPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l1At, hc10, hc11, hc12, hc13, hrun, hcode, hdest, hdest',
      jumpDest4731, hpaj, hpam, UInt256.eq, UInt256.isTrue,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

def gasSteps_selectExit (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hn32 : n ≤ 32) (hj : j = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (l1At 4448 s mem bi pa pb n i j pdst ret rest) (l1At 4731 s mem bi pa pb n i j pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectBlock hcode hfork
    (run_selectExit s mem bi pa pb n i j pdst ret rest hcap hrun hcode hn32 hj hpa hpaFit) hrun hnp

set_option linter.unusedSimpArgs false in
theorem run_join (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock joinBlock
      (l1At 4731 s mem bi pa pb n i j pdst ret rest) = some (midState s (l1Step mem bi pa n j).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) j))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) j))
        (l1Step mem bi pa n j).carry bi pa pb n i pdst ret rest) := by
  have hc : rest.length + 10 < 1024 := by omega
  simp [joinBlock, Cios2Paths.L1.joinPC, Cios2Paths.L1.joinStartIndex,
    Cios2Paths.L1.joinOpAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    l1At, midState, hc, hrun, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_join (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (l1At 4731 s mem bi pa pb n i j pdst ret rest) (midState s (l1Step mem bi pa n j).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) j))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) j))
        (l1Step mem bi pa n j).carry bi pa pb n i pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka joinBlock hcode hfork
    (run_join s mem bi pa pb n i j pdst ret rest hcap hrun) hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac
