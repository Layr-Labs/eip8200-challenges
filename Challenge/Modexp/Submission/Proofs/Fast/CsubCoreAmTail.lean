import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreAmLoop
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
/-- The `ADDMOD` loop exit (pc 2213): the loop has run `n` times and the three
pointers plus the carry are still on the stack. -/
def amTailState (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2015
           stack := [UInt256.ofNat (ptrAt (2080 + 32 * n) j),
                     UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) j),
                     (amStep memory pa pb n j).flag, pd, ret] ++ rest
           memory := (amStep memory pa pb n j).memory }

/-- Entry of `CSUB` (pc 2220) with stack `[pd, ret]`. -/
def subEntryState (s : State) (memory : ByteArray) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4847
           stack := [pdst, ret] ++ rest
           memory := memory }

/-- Entry of the high-limb guard with the original destination and return stack. -/
def csEntryState (s : State) (memory : ByteArray) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4667, stack := [pdst, ret] ++ rest, memory := memory }

set_option linter.unusedSimpArgs false in
theorem run_amLoopExit (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 91 ≤ s.activeWords.toNat)
    (hj : j + 1 = n) (hn32 : n ≤ 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 2912)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2912) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1627
      (amLoopState s memory pa pb n j pd ret rest) =
      some (amTailState s memory pa pb n (j + 1) pd ret rest) := by
  have hbig : (2912 : Nat) < 2 ^ 256 := by norm_num
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hnj : n - 1 - j = 0 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h8224 : (2080 : UInt256).toNat = 2080 := by decide
  have hta : ptrAt (pa + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have htb : ptrAt (pb + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have htt : ptrAt (2080 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      2112 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hnext : ptrAt (2080 + 32 * n) (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      2080 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat pa 32) =
      s.activeWords := activeWords_fix s pa 32 (by decide) (by omega) hact
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat pb 32) =
      s.activeWords := activeWords_fix s pb 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2112 32) =
      s.activeWords := activeWords_fix s 2112 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk1627, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      amLoopState, amTailState, amStep, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hc6, hc7, hc8, hc9, hrun, hK, h8224, hnj,
      hta, htb, htt, hnext, hactA, hactB, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_amTail (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 91 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1662
      (amTailState s memory pa pb n j pd ret rest) =
      some (csEntryState s
        (MachineState.writeBytes (amStep memory pa pb n j).memory
          (Data.Bytes.natToBytesPadded (amStep memory pa pb n j).flag.toNat 32) 2080)
        pd ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h8224 : (2080 : UInt256).toNat = 2080 := by decide
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have h3811 : (4667 : UInt256).toNat = 4667 := by decide
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4667 = true := by
    rw [hcode]; exact jumpDest4976
  simp (config := { maxSteps := 400000 })
    [blk1662, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      amTailState, csEntryState, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hc2, hc3, hc4, hc5, hc6, hrun, h8224, hactT, h3811, hjd,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  rfl


/-! ## The `CSUB` subroutine -/





end Challenge.Modexp.Submission.Proofs.Fast.Csub
