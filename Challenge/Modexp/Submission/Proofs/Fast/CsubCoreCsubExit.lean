import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreCsubLoop
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
attribute [local simp] jumpDestCopyResume
set_option linter.unusedSimpArgs false in
theorem run_csLoopExit (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 91 ≤ s.activeWords.toNat)
    (hj : j + 1 = n) (hn32 : n ≤ 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1683
      (csLoopState s memory n j pdst ret rest) =
      some (csTailState s memory n (j + 1) pdst ret rest) := by
  have hbig : (20000 : Nat) < 2 ^ 256 := by norm_num
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hnj : n - 1 - j = 0 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h8224 : (2080 : UInt256).toNat = 2080 := by decide
  have ht : ptrAt (2080 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      2112 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hm : ptrAt (32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hd : ptrAt (1760 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      1792 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hnext : ptrAt (2080 + 32 * n) (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      2080 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2112 32) =
      s.activeWords := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := activeWords_fix s 0 32 (by decide) (by omega) hact
  have hactD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1792 32) =
      s.activeWords := activeWords_fix s 1792 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk1683, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csLoopState, csTailState, csStep, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hc6, hc7, hc8, hc9, hc10, hrun, hK, h8224, hnj,
      ht, hm, hd, hnext, hactT, hactM, hactD, ptrAt_succ,
      UInt256.gt, UInt256.lt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]


end Challenge.Modexp.Submission.Proofs.Fast.Csub
