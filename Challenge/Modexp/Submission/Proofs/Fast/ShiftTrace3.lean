import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace2
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Block reductions of the shift-reduce base conversion, part 3

The middle block, the two repair loops, the `CSUB` call and the loop exits.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

attribute [local simp] CompactConstants.notThirtyOne notThirtyOneOfNat

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

/-- `GT a b` is `LT b a`.  The middle block computes both flags with `GT`
(`[s, c, q]` ↦ `GT c s`, `GT q s`); rewriting every `GT` to `LT` puts the
block's jump condition and the model's `negOf` into the same normal form. -/
theorem midGtSwap (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := rfl

theorem isTrue_lor_left (a b : UInt256) (ha : a.toNat ≠ 0) :
    UInt256.isTrue (UInt256.lor a b) := by
  show (UInt256.lor a b).toNat ≠ 0
  intro h
  have h0 : UInt256.lor a b = 0 := Challenge.EvmProof.Word.word_ext (h.trans (by decide))
  apply ha
  rw [((WindowGuardLogic.wordOr_eq_zero_iff a b).1 h0).1] <;> decide

theorem isTrue_lor_right (a b : UInt256) (hb : b.toNat ≠ 0) :
    UInt256.isTrue (UInt256.lor a b) := by
  show (UInt256.lor a b).toNat ≠ 0
  intro h
  have h0 : UInt256.lor a b = 0 := Challenge.EvmProof.Word.word_ext (h.trans (by decide))
  apply hb
  rw [((WindowGuardLogic.wordOr_eq_zero_iff a b).1 h0).2] <;> decide

theorem isTrue_lor_of (a b : UInt256) (h : a.toNat ≠ 0 ∨ b.toNat ≠ 0) :
    UInt256.isTrue (UInt256.lor a b) := by
  rcases h with h | h
  · exact isTrue_lor_left a b h
  · exact isTrue_lor_right a b h

theorem midMem_tn (mem : ByteArray) (c q : UInt256) :
    MachineState.readWord (midMem mem c q) 2080 = tnOf mem c q := by
  unfold midMem Exp.storeWord
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem subRounds_shift (mem : ByteArray) (n : Nat) :
    ∀ i, subRounds (subRoundMem mem n) n i = subRounds mem n (i + 1)
  | 0 => rfl
  | i + 1 => by
      show subRoundMem (subRounds (subRoundMem mem n) n i) n =
        subRoundMem (subRounds mem n (i + 1)) n
      rw [subRounds_shift mem n i]

/-- `blk3125` with `neg ||| TN ≠ 0`: store `TN`, jump to `UNC` with `neg` above `k`. -/
theorem run_mid_unc (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hor : (negOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q).toNat ≠ 0 ∨ (tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q).toNat ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3125
      (midState s um q n bsize esize msize k) =
      some (uncState s (midMem (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) n bsize esize msize k
        (negOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q)) := by
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hor1 : UInt256.isTrue (UInt256.lor (negOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) (tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q)) := isTrue_lor_of _ _ hor
  have hor2 : UInt256.isTrue (UInt256.lor (tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) (negOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q)) := isTrue_lor_of _ _ hor.symm
  unfold negOf bwOf cwOf tnOf wN at hor1 hor2
  simp only [midGtSwap] at hor1 hor2
  simp (config := { maxSteps := 500000 })
    [blk3125, midGtSwap, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      midState, uncState, pcMid, pcUnc, midMem, negOf, bwOf, cwOf, tnOf, wN, Exp.storeWord,
      outer, Exp.outer, hcode, hrun, hTN, hor1, hor2, jumpDestUnc,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `blk3125` with `neg = 0` and `TN = 0`: fall into the `CSUB` call with `[0, k]`. -/
theorem run_mid_zero (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hneg : negOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q = UInt256.ofNat 0)
    (htz : tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3125
      (midState s um q n bsize esize msize k) =
      some (csubCallState s (midMem (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) n bsize esize msize k) := by
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hz : ¬ UInt256.isTrue (UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0)) := by decide
  have hz1 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
  have hz2 : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hmem : midMem (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q = Exp.storeWord (Monpro.l1Step um q NEG n n).memory 2080 (UInt256.ofNat 0) := by
    unfold midMem; rw [htz]
  rw [hmem]
  unfold negOf bwOf cwOf wN at hneg
  unfold tnOf wN at htz
  simp only [midGtSwap] at hneg
  simp (config := { maxSteps := 500000 })
    [blk3125, midGtSwap, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      midState, csubCallState, pcMid, pcCsubCall, Exp.storeWord,
      outer, Exp.outer, hcode, hrun, hTN, hneg, htz, hz, hz1, hz2,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `UNC` with `neg ≠ 0`: fall into `ADD_LOOP`. -/
theorem run_unc_add (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) (f : UInt256)
    (hf : f.toNat ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkUnc
      (uncState s mem n bsize esize msize k f) =
      some (addLoopState s mem n bsize esize msize k) := by
  simp (config := { maxSteps := 200000 })
    [blkUnc, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      uncState, addLoopState, kState, pcUnc, pcAddLoop,
      outer, Exp.outer, hcode, hrun, hf, jumpDestSubl, UInt256.isZero, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `UNC` with `neg = 0`: jump to `SUBL`. -/
theorem run_unc_sub (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) (f : UInt256)
    (hf : f.toNat = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkUnc
      (uncState s mem n bsize esize msize k f) =
      some (subEntryState s mem n bsize esize msize k) := by
  simp (config := { maxSteps := 200000 })
    [blkUnc, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      uncState, subEntryState, kState, pcUnc, pcSubEntry,
      outer, Exp.outer, hcode, hrun, hf, jumpDestSubl, UInt256.isZero, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `blk3153`: the add round's frame `[p, 0, k]`. -/
theorem run_addEntry (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3153
      (addLoopState s mem n bsize esize msize k) =
      some (addInnerState s mem n bsize esize msize k 0) := by
  have hTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2784 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 200000 })
    [blk3153, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      addLoopState, addInnerState, kState, pcAddLoop, pcAddInner, addStep,
      outer, Exp.outer, hcode, hrun, htl, hTL, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3157a`: one limb of the add pass, up to `OR`, with the loop pointer
`p` abstract. -/
theorem run_addBodyA (s : State) (mem : ByteArray) (p : UInt256) (n bsize esize msize k j : Nat)
    (hn32 : n ≤ 8) (hj : j < n) (hpv : p.toNat = 2112 + 32 * (n - 1 - j))
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3157a
      { s with pc := UInt256.ofNat pcAddInner
               stack := p :: (addStep mem n j).flag :: UInt256.ofNat k :: outer n bsize esize msize
               memory := (addStep mem n j).memory } =
      some { s with pc := UInt256.ofNat pcAddMid
                    stack := (addStep mem n (j + 1)).flag :: p :: UInt256.ofNat k ::
                      outer n bsize esize msize
                    memory := (addStep mem n (j + 1)).memory } := by
  have hsub : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + (2112 + 32 * (n - 1 - j)) - 2112) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32 * (n - 1 - j) := by
    rw [show 115792089237316195423570985008687907853269984665640564039457584007913129639936 + (2112 + 32 * (n - 1 - j)) - 2112 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 + 32 * (n - 1 - j) by omega,
      Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (2112 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [blk3157a, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcAddInner, pcAddMid, addStep,
      outer, Exp.outer, hcode, hrun, hpv, hsub, hactT, hactM,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.ofNat_sub_ofNat, Nat.mod_eq_of_lt, List.exchange]

/-- `blk3157b` with limbs to go: pointer step and back to the inner loop head. -/
theorem run_addTail_go (s : State) (mm : ByteArray) (c p p' : UInt256)
    (n bsize esize msize k : Nat)
    (hp' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + p = p')
    (hgt : 2111 < p'.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3157b
      { s with pc := UInt256.ofNat pcAddMid
               stack := c :: p :: UInt256.ofNat k :: outer n bsize esize msize
               memory := mm } =
      some { s with pc := UInt256.ofNat pcAddInner
                    stack := p' :: c :: UInt256.ofNat k :: outer n bsize esize msize
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3157b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcAddMid, pcAddInner, outer, Exp.outer, hcode, hrun, hp', hgt, jumpDest5121,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]

/-- `blk3157b` after the last limb: pointer step and fall into the tail. -/
theorem run_addTail_last (s : State) (mm : ByteArray) (c p p' : UInt256)
    (n bsize esize msize k : Nat)
    (hp' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + p = p')
    (hle : p'.toNat = 2080)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3157b
      { s with pc := UInt256.ofNat pcAddMid
               stack := c :: p :: UInt256.ofNat k :: outer n bsize esize msize
               memory := mm } =
      some { s with pc := UInt256.ofNat pcAddTail
                    stack := p' :: c :: UInt256.ofNat k :: outer n bsize esize msize
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3157b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcAddMid, pcAddTail, outer, Exp.outer, hcode, hrun, hp', hle, jumpDest5121,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]

/-- `blk3192` without a carry out of `TN`: another round. -/
theorem run_addTail_again (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hout : addOut mem n = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3192
      (addTailState s mem n bsize esize msize k) =
      some (addLoopState s (addRoundMem mem n) n bsize esize msize k) := by
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hc : UInt256.isTrue (UInt256.isZero (addOut mem n)) := by rw [hout]; decide
  unfold addOut addCarry at hc
  simp (config := { maxSteps := 300000 })
    [blk3192, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      addTailState, addLoopState, kState, pcAddTail, pcAddLoop, addRoundMem, addCarry,
      Exp.storeWord, outer, Exp.outer, hcode, hrun, hTN, hc, jumpDest5115,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3192` with a carry out of `TN`: the value is non-negative, go to `SUB_CHECK`. -/
theorem run_addTail_done (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hout : addOut mem n = UInt256.ofNat 1)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3192
      (addTailState s mem n bsize esize msize k) =
      some (subCheckState s (addRoundMem mem n) n bsize esize msize k) := by
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hc : ¬ UInt256.isTrue (UInt256.isZero (addOut mem n)) := by rw [hout]; decide
  unfold addOut addCarry at hc
  simp (config := { maxSteps := 300000 })
    [blk3192, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      addTailState, subCheckState, kState, pcAddTail, pcSubCheck, addRoundMem, addCarry,
      Exp.storeWord, outer, Exp.outer, hcode, hrun, hTN, hc, jumpDest5115,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3204` with `TN = 0`: jump to the `CSUB` call with `[TN, k]`. -/
theorem run_subCheck_done (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (htn : (MachineState.readWord mem 2080).toNat = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3204
      (subCheckState s mem n bsize esize msize k) =
      some (csubCallState s mem n bsize esize msize k) := by
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0 :=
    Challenge.EvmProof.Word.word_ext (by rw [htn] <;> decide)
  simp (config := { maxSteps := 200000 })
    [blk3204, opAt, pushAt, wfOp, htn0,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      subCheckState, csubCallState, kState, pcSubCheck, pcCsubCall,
      outer, Exp.outer, hcode, hrun, hTN, htn, jumpDest5311, UInt256.isZero, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3204g` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
theorem run_subCheck_go (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (htn : (MachineState.readWord mem 2080).toNat ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3204g
      (subCheckState s mem n bsize esize msize k) =
      some (subEntryState s mem n bsize esize msize k) := by
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 200000 })
    [blk3204g, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      subCheckState, subEntryState, kState, pcSubCheck, pcSubEntry,
      outer, Exp.outer, hcode, hrun, hTN, htn, UInt256.isZero, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, jumpDest5311]

/-- `blk3210`: the subtract round's frame `[p, 0]`. -/
theorem run_subEntry (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3210
      (subEntryState s mem n bsize esize msize k) =
      some (subInnerState s mem n bsize esize msize k 0) := by
  have hTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2784 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 200000 })
    [blk3210, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      subEntryState, subInnerState, kState, pcSubEntry, pcSubInner, subStep,
      outer, Exp.outer, hcode, hrun, htl, hTL, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3213a`: one limb of the subtract pass, up to `OR`, with the loop pointer
`p` abstract. -/
theorem run_subBodyA (s : State) (mem : ByteArray) (p : UInt256) (n bsize esize msize k j : Nat)
    (hn32 : n ≤ 8) (hj : j < n) (hpv : p.toNat = 2112 + 32 * (n - 1 - j))
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3213a
      { s with pc := UInt256.ofNat pcSubInner
               stack := p :: (subStep mem n j).flag :: UInt256.ofNat k :: outer n bsize esize msize
               memory := (subStep mem n j).memory } =
      some { s with pc := UInt256.ofNat pcSubMid
                    stack := (subStep mem n (j + 1)).flag :: p :: (subStep mem n j).flag ::
                      UInt256.ofNat k :: outer n bsize esize msize
                    memory := (subStep mem n (j + 1)).memory } := by
  have hsub : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + (2112 + 32 * (n - 1 - j)) - 2112) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32 * (n - 1 - j) := by
    rw [show 115792089237316195423570985008687907853269984665640564039457584007913129639936 + (2112 + 32 * (n - 1 - j)) - 2112 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 + 32 * (n - 1 - j) by omega,
      Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (2112 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [blk3213a, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcSubInner, pcSubMid, subStep,
      outer, Exp.outer, hcode, hrun, hpv, hsub, hactT, hactM,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.ofNat_sub_ofNat, Nat.mod_eq_of_lt, List.exchange]

/-- `blk3213b` with limbs to go: pointer step and back to the inner loop head. -/
theorem run_subTail_go (s : State) (mm : ByteArray) (c p p' : UInt256) (f : UInt256)
    (n bsize esize msize k : Nat)
    (hp' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + p = p')
    (hgt : 2111 < p'.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3213b
      { s with pc := UInt256.ofNat pcSubMid
               stack := c :: p :: f :: UInt256.ofNat k :: outer n bsize esize msize
               memory := mm } =
      some { s with pc := UInt256.ofNat pcSubInner
                    stack := p' :: c :: UInt256.ofNat k :: outer n bsize esize msize
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3213b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcSubMid, pcSubInner, outer, Exp.outer, hcode, hrun, hp', hgt, jumpDest5227,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]

/-- `blk3213b` after the last limb: pointer step and fall into the tail. -/
theorem run_subTail_last (s : State) (mm : ByteArray) (c p p' : UInt256) (f : UInt256)
    (n bsize esize msize k : Nat)
    (hp' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + p = p')
    (hle : p'.toNat = 2080)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3213b
      { s with pc := UInt256.ofNat pcSubMid
               stack := c :: p :: f :: UInt256.ofNat k :: outer n bsize esize msize
               memory := mm } =
      some { s with pc := UInt256.ofNat pcSubTail
                    stack := p' :: c :: UInt256.ofNat k :: outer n bsize esize msize
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3213b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcSubMid, pcSubTail, outer, Exp.outer, hcode, hrun, hp', hle, jumpDest5227,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]

/-- `blk3245`: `TN -= borrow`, back to `SUB_CHECK`. -/
theorem run_subTail (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3245
      (subTailState s mem n bsize esize msize k) =
      some (subCheckState s (subRoundMem mem n) n bsize esize msize k) := by
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 300000 })
    [blk3245, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      subTailState, subCheckState, kState, pcSubTail, pcSubCheck, subRoundMem, subBorrow,
      Exp.storeWord, outer, Exp.outer, hcode, hrun, hTN, jumpDest5247,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3253`: `k := k - 1` (`NOT ADD` on the zero above `k`), then call `CSUB(BASE)` returning straight to the loop head. -/
theorem run_csubCall (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hk : 1 ≤ k) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3253
      (csubCallState s mem n bsize esize msize k) =
      some (Csub.csEntryState s mem (UInt256.ofNat 512) (UInt256.ofNat pcAfterCsub)
        (UInt256.ofNat (k - 1) :: outer n bsize esize msize)) := by
  have hdec : UInt256.lnot (UInt256.ofNat 0) + UInt256.ofNat k =
      UInt256.ofNat (k - 1) := by
    interval_cases k <;> decide
  have hdec' : UInt256.lnot (0 : UInt256) + UInt256.ofNat k = UInt256.ofNat (k - 1) := hdec
  simp (config := { maxSteps := 200000 })
    [blk3253, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csubCallState, kState, pcCsubCall, pcAfterCsub, Csub.csEntryState,
      outer, Exp.outer, hcode, hrun, hdec, hdec', jumpDest4976,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `blk3264`: drop the counter, copy the conversion's result from `0x1400` into
`R1 = 0x0400` and jump to the dispatcher.

The `MCOPY` is the conversion's own: it computes into `0x1400`, and in the
previous layout `R1` was filled by the call `Setup.setupPathD` used to make.  That call now
happens only on the recogniser-miss route (`ShiftTrace1.run_miss`), so the conversion itself
re-establishes `R1` here for the generic route that follows.  The copy length is the
configuration word `V_S32 = 0x2480`, i.e. `32 * n`. -/
theorem run_shiftDone (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hact : 88 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3264
      (frameState s mem 3535 n bsize esize msize) =
      some { Exp.bDone s (Exp.mcopyMem mem 1024 1280 (32 * n)) n bsize esize msize with
               pc := UInt256.ofNat 2637 } := by
  have hsize : (UInt256.ofNat (32 * n)).toNat = 32 * n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by decide)
  have hawDst : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 1024 (32 * n)) = s.activeWords :=
    Monpro.activeWords_fix s 1024 (32 * n) (by omega) (by omega) (by omega)
  have hawSrc : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 1280 (32 * n)) = s.activeWords :=
    Monpro.activeWords_fix s 1280 (32 * n) (by omega) (by omega) (by omega)
  -- This block's high-water mark is fixed THREE times, not once: the `MLOAD` of `V_S32` at 2688
  -- and then the `MCOPY`'s destination 1024 and source 1280.  A composed `UInt256`-level fact
  -- cannot close that, because the nesting is `activeWordsAfter (activeWordsAfter (... % 2^256))`
  -- and simp meets the layers one at a time.  So give it NAT-level rewrites -- the same shape
  -- `StagedOperandEntryZero` already uses -- and one identity to finish.  `Exp.activeWords_fix2`
  -- is the ready-made two-region lemma but wants `297 <= activeWords` where this block has 296;
  -- `Monpro.activeWordsAfter_fix` carries the 296 bound.
  have hactN : s.activeWords.toNat %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.activeWords.toNat := Nat.mod_eq_of_lt s.activeWords.val.isLt
  have haw9344 : MachineState.activeWordsAfter s.activeWords.toNat 2688 32 =
      s.activeWords.toNat :=
    Monpro.activeWordsAfter_fix s.activeWords.toNat 2688 32 (by decide) (by omega) hact
  have haw4096 : MachineState.activeWordsAfter s.activeWords.toNat 1024 (32 * n) =
      s.activeWords.toNat :=
    Monpro.activeWordsAfter_fix s.activeWords.toNat 1024 (32 * n) (by omega) (by omega) hact
  have haw5120 : MachineState.activeWordsAfter s.activeWords.toNat 1280 (32 * n) =
      s.activeWords.toNat :=
    Monpro.activeWordsAfter_fix s.activeWords.toNat 1280 (32 * n) (by omega) (by omega) hact
  have hawId : UInt256.ofNat s.activeWords.toNat = s.activeWords :=
    (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  simp (config := { maxSteps := 400000 })
    [blk3264, opAt, pushAt, wfOp, hs32, hsize, hawDst, hawSrc, Exp.mcopyMem,
      hactN, haw9344, haw4096, haw5120, hawId,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      frameState, Exp.bDone,
      outer, Exp.outer, hcode, hrun, jumpDest3412,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.Shift
