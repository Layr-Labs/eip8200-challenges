import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Core

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Mid

theorem jumpDest5254 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5254 = true := by
  exact Artifact.isValidJumpDest_index 3365 (by rfl)

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_selectContinue (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hn32 : n ≤ 32) (hj : k + 1 < n) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectBlock
      (l2At 5050 s mid bi mu c0 pa pb n i k pdst ret rest) = some (l2At 5059 s mid bi mu c0 pa pb n i k pdst ret rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hdest : (5254 : UInt256).toNat = 5254 := by decide
  have hdest' : (5254 : UInt256) = UInt256.ofNat 5254 := by decide
  have hptj : ptrAt (8192 + 32 * n) k % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8192 + 32 * (n - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have hne : 8192 + 32 * (n - k) ≠ 8224 := by omega
  simp (config := { maxSteps := 800000 })
    [selectBlock, Cios2Paths.L2Pair.selectPC, Cios2Paths.L2Pair.selectStartIndex,
      Cios2Paths.L2Pair.selectOpAt, Cios2Paths.L2Pair.selectPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l2At, hc10, hc11, hc12, hc13, hrun, hcode, hdest, hdest',
      jumpDest5254, hptj, h8224, hne, UInt256.eq, UInt256.isTrue,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

def gasSteps_selectContinue (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hn32 : n ≤ 32) (hj : k + 1 < n) :
    Challenge.EvmProof.GasSteps (l2At 5050 s mid bi mu c0 pa pb n i k pdst ret rest) (l2At 5059 s mid bi mu c0 pa pb n i k pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectBlock hcode hfork
    (run_selectContinue s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun hcode hn32 hj) hrun hnp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_selectExit (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hn32 : n ≤ 32) (hj : k + 1 = n) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectBlock
      (l2At 5050 s mid bi mu c0 pa pb n i k pdst ret rest) = some (l2At 5254 s mid bi mu c0 pa pb n i k pdst ret rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hdest : (5254 : UInt256).toNat = 5254 := by decide
  have hdest' : (5254 : UInt256) = UInt256.ofNat 5254 := by decide
  have hptj : ptrAt (8192 + 32 * n) k % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224 := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  simp (config := { maxSteps := 800000 })
    [selectBlock, Cios2Paths.L2Pair.selectPC, Cios2Paths.L2Pair.selectStartIndex,
      Cios2Paths.L2Pair.selectOpAt, Cios2Paths.L2Pair.selectPushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      l2At, hc10, hc11, hc12, hc13, hrun, hcode, hdest, hdest',
      jumpDest5254, hptj, h8224, UInt256.eq, UInt256.isTrue,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

def gasSteps_selectExit (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hn32 : n ≤ 32) (hj : k + 1 = n) :
    Challenge.EvmProof.GasSteps (l2At 5050 s mid bi mu c0 pa pb n i k pdst ret rest) (l2At 5254 s mid bi mu c0 pa pb n i k pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectBlock hcode hfork
    (run_selectExit s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun hcode hn32 hj) hrun hnp

set_option linter.unusedSimpArgs false in
theorem run_join (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock joinBlock
      (l2At 5254 s mid bi mu c0 pa pb n i k pdst ret rest) = some (tailState s (l2Step mid mu c0 n k).memory
        (UInt256.ofNat (ptrAt (32 * n - 64) k))
        (UInt256.ofNat (ptrAt (8192 + 32 * n) k))
        (l2Step mid mu c0 n k).carry mu bi pa pb n i pdst ret rest) := by
  have hc : rest.length + 11 < 1024 := by omega
  simp [joinBlock, Cios2Paths.L2Pair.joinPC, Cios2Paths.L2Pair.joinStartIndex,
    Cios2Paths.L2Pair.joinOpAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    l2At, tailState, hc, hrun, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_join (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (l2At 5254 s mid bi mu c0 pa pb n i k pdst ret rest) (tailState s (l2Step mid mu c0 n k).memory
        (UInt256.ofNat (ptrAt (32 * n - 64) k))
        (UInt256.ofNat (ptrAt (8192 + 32 * n) k))
        (l2Step mid mu c0 n k).carry mu bi pa pb n i pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka joinBlock hcode hfork
    (run_join s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun) hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair
