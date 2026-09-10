import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart11

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

theorem run_amLoopBody (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 < n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1627
      (amLoopState s memory pa pb n j pd ret rest) =
      some (amLoopState s memory pa pb n (j + 1) pd ret rest) := by
  have hbig : (9472 : Nat) < 2 ^ 256 := by norm_num
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h2500 : (2087 : UInt256).toNat = 2087 := by decide
  have h2500' : (2087 : UInt256) = UInt256.ofNat 2087 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (2087 : UInt256).toNat = true := by
    rw [h2500]; exact jumpDest2168
  have hta : ptrAt (pa + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have htb : ptrAt (pb + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have htt : ptrAt (8224 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hnext : ptrAt (8224 + 32 * n) (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hgt : 8224 < 8224 + 32 * (n - 1 - j) := by omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pb + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk1627, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      amLoopState, amStep, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hc6, hc7, hc8, hc9, hrun, hcode, hK, h8224, h2500, h2500', hjump, jumpDest2168,
      hta, htb, htt, hnext, hgt, hactA, hactB, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
