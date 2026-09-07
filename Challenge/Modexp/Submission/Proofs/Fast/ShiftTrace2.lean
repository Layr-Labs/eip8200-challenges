import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace1

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Block reductions of the shift-reduce base conversion, part 2

The shift loop: `u` construction, the quotient estimate, the limb pass, the
middle block, the repair rounds, the `CSUB` call and the exits.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

/-- `blk3013` with steps to go: fall into the body. -/
theorem run_shiftHead_go (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hk : k ≠ 0) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013
      (shiftLoopState s mem n bsize esize msize k) =
      some (shiftBodyState s mem n bsize esize msize k) := by
  have hkmod : k % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = k := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 200000 })
    [blk3013, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftBodyState, kState, pcShiftLoop, pcShiftBody,
      outer, Exp.outer, hcode, hrun, hk, hkmod, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, jumpDest5366]

/-- `blk3013` with no steps to go: jump to `SHIFT_DONE`. -/
theorem run_shiftHead_done (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013
      (shiftLoopState s mem n bsize esize msize 0) =
      some (shiftDoneState s mem n bsize esize msize) := by
  simp (config := { maxSteps := 200000 })
    [blk3013, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftDoneState, kState, pcShiftLoop, pcShiftDone,
      outer, Exp.outer, hcode, hrun, jumpDest5366, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3018`: `MCOPY(TN, BASE, s32)` and `t[0] := 0`. -/
theorem run_shiftBody (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3018
      (shiftBodyState s mem n bsize esize msize k) =
      some (estimateState s mem n bsize esize msize k) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * n := Exp.mod_word_self (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix2 : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 (32 * n)) 2048
      (32 * n)) = s.activeWords :=
    Exp.activeWords_fix2 s 8224 (32 * n) 2048 (32 * n) (by omega) (by omega) (by omega)
      (by omega) hact
  have hfixTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have hfixT0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8224 + 32 * n) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have htl' : MachineState.readWord
      (MachineState.writeBytes mem (MachineState.readPadded mem 2048 (32 * n)) 8224) 9440 =
      UInt256.ofNat (8224 + 32 * n) := by
    rw [show MachineState.writeBytes mem (MachineState.readPadded mem 2048 (32 * n)) 8224 =
      Exp.mcopyMem mem 8224 2048 (32 * n) from rfl]
    rw [Exp.readWord_mcopyMem_disjoint mem 8224 2048 (32 * n) 9440 (Or.inr (by omega))]
    exact htl
  have hmodTL : (8224 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8224 + 32 * n := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 400000 })
    [blk3018, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftBodyState, estimateState, kState, pcShiftBody, pcEstimate, uMem,
      Exp.mcopyMem, Exp.storeWord, outer, Exp.outer, hcode, hrun, hmod, hfix2, hfixTL,
      hfixT0, htl', hmodTL, Exp.push0_word,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3026`: quotient estimate with a branchless saturation mask. -/
theorem run_estimate (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3026
      (estimateState s mem n bsize esize msize k) =
      some (macSetupState s mem n bsize esize msize k) := by
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2048 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6144 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hC : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6208 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hE : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6176 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hF : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6240 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hG : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6272 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [blk3026, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      estimateState, macSetupState, kState, pcEstimate, pcMacSetup, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, hA, hB, hC, hD, hE, hF, hG, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, Monpro.zero_lt_eq_double_isZero]

/-- `blk3069`: the limb-pass frame `[paj, ptj, 0, q]`. -/
theorem run_macSetup (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hact : 296 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord (uMem mem n) 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord (uMem mem n) 9408 = UInt256.ofNat (32 * n - 32))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3069
      (macSetupState s mem n bsize esize msize k) =
      some (macLoopState s (uMem mem n) (qhatOf (uMem mem n)) n bsize esize msize k 0) := by
  have hTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hML : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9408 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpa : UInt256.ofNat (5120 + (32 * n - 32)) = UInt256.ofNat (NEG + 32 * n - 32) := by
    unfold NEG; congr 1; omega
  simp (config := { maxSteps := 300000 })
    [blk3069, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      macSetupState, macLoopState, pcMacSetup, pcMacLoop, Monpro.l1Step,
      outer, Exp.outer, hcode, hrun, htl, hml, hTL, hML, Exp.push0_word, hpa,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  all_goals (try (congr 1; unfold NEG; omega))

/-- `blk3077a`: one limb of `t += q * NEG` with both pointer steps, up to the
exit test.  The pointers stay abstract. -/
theorem run_macBodyA (s : State) (um : ByteArray) (q pa pt pa' pt' : UInt256)
    (n bsize esize msize k j : Nat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j < n)
    (hpa : pa.toNat = NEG + 32 * (n - 1 - j)) (hpt : pt.toNat = 8256 + 32 * (n - 1 - j))
    (hpa' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pa = pa')
    (hpt' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pt = pt') :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3077a
      { s with pc := UInt256.ofNat pcMacLoop
               stack := pa :: pt :: (Monpro.l1Step um q NEG n j).carry :: q :: UInt256.ofNat k ::
                 outer n bsize esize msize
               memory := (Monpro.l1Step um q NEG n j).memory } =
      some { s with pc := UInt256.ofNat pcMacTail
                    stack := pa' :: pt' :: (Monpro.l1Step um q NEG n (j + 1)).carry :: q ::
                      UInt256.ofNat k :: outer n bsize esize msize
                    memory := (Monpro.l1Step um q NEG n (j + 1)).memory } := by
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (NEG + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by unfold NEG; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk3077a, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcMacLoop, pcMacTail, Monpro.l1Step, Monpro.macSum, Monpro.macCarry, Monpro.mulHi,
      Monpro.maxWord_literal, outer, Exp.outer,
      hrun, hcode, negK_literal, hpa, hpt, hpa', hpt', hactA, hactT,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  refine ⟨?_, Monpro.MacAlt.macCarryFix _ _ _ _⟩
  rw [Monpro.MacAlt.macSumNat]

/-- `blk3077b` with limbs to go: back to the loop head. -/
theorem run_macTail_go (s : State) (mm : ByteArray) (pa pt c q : UInt256)
    (n bsize esize msize k : Nat) (hgt : 8224 < pt.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3077b
      { s with pc := UInt256.ofNat pcMacTail
               stack := pa :: pt :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
               memory := mm } =
      some { s with pc := UInt256.ofNat pcMacLoop
                    stack := pa :: pt :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3077b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcMacTail, pcMacLoop, outer, Exp.outer, hcode, hrun, hgt, jumpDest4968,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt]

/-- `blk3077b` after the last limb: fall through into the middle block. -/
theorem run_macTail_exit (s : State) (mm : ByteArray) (pa pt c q : UInt256)
    (n bsize esize msize k : Nat) (hpt : pt.toNat = 8224)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3077b
      { s with pc := UInt256.ofNat pcMacTail
               stack := pa :: pt :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
               memory := mm } =
      some { s with pc := UInt256.ofNat pcMid
                    stack := pa :: pt :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3077b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcMacTail, pcMid, outer, Exp.outer, hcode, hrun, hpt, jumpDest4968,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt]

end Challenge.Modexp.Submission.Proofs.Fast.Shift
