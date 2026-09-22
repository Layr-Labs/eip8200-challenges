import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace2
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic
import Challenge.Modexp.Submission.Proofs.Fast.RetainedTEntry

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


/-- `blk3125` with `neg ||| TN ≠ 0`: store `TN`, jump to `UNC` with `neg` above `k`. -/
theorem run_mid_unc (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hn32 : n ≤ 8)
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
  have hslot : ∀ (v : Nat) (a : Nat), a + 32 ≤ 2048 →
      MachineState.readWord (MachineState.writeBytes (Monpro.l1Step um q NEG n n).memory
        (Data.Bytes.natToBytesPadded v 32) 2080) a = MachineState.readWord um a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 2080
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Monpro.readWord_l1Step um q NEG n a n hn32 (Or.inl ha)]
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
      hslot, entrySlots, rideSlots,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `blk3125` with `neg = 0` and `TN = 0`: fall into the `CSUB` call with `[0, k]`. -/
theorem run_mid_zero (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hn32 : n ≤ 8)
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
  have hslot : ∀ (v : Nat) (a : Nat), a + 32 ≤ 2048 →
      MachineState.readWord (MachineState.writeBytes (Monpro.l1Step um q NEG n n).memory
        (Data.Bytes.natToBytesPadded v 32) 2080) a = MachineState.readWord um a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 2080
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Monpro.readWord_l1Step um q NEG n a n hn32 (Or.inl ha)]
  unfold negOf bwOf cwOf wN at hneg
  unfold tnOf wN at htz
  rw [hmem]
  simp only [midGtSwap] at hneg
  simp (config := { maxSteps := 1500000 })
    [blk3125, midGtSwap, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      midState, csubCallState, pcMid, pcCsubCall, Exp.storeWord, entrySlots, rideSlots,
      outer, Exp.outer, hcode, hrun, hTN, hneg, htz, hz, hz1, hz2,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      hslot,
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
      uncState, addLoopState, slotKState, rideSlots, entrySlots, shiftEntry, pcUnc, pcAddLoop,
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
      addLoopState, addInnerState, slotKState, rideSlots, entrySlots, shiftEntry, pcAddLoop, pcAddInner, addStep,
      outer, Exp.outer, hcode, hrun, htl, hTL, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3157a`: one limb of the add pass, up to `OR`, with the loop pointer
`p` abstract. -/
theorem run_addBodyA (s : State) (mem : ByteArray) (p : UInt256) (n bsize esize msize k j : Nat)
    (rest : List UInt256)
    (hn32 : n ≤ 8) (hj : j < n) (hpv : p.toNat = 2112 + 32 * (n - 1 - j))
    (hcap : rest.length ≤ 1011)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3157a
      { s with pc := UInt256.ofNat pcAddInner
               stack := p :: (addStep mem n j).flag :: UInt256.ofNat k :: rest
               memory := (addStep mem n j).memory } =
      some { s with pc := UInt256.ofNat pcAddMid
                    stack := p :: (addStep mem n (j + 1)).flag :: UInt256.ofNat k :: rest
                    memory := (addStep mem n (j + 1)).memory } := by
  have hg3 : rest.length + 3 < 1024 := by omega
  have hg4 : rest.length + 4 < 1024 := by omega
  have hg5 : rest.length + 5 < 1024 := by omega
  have hg6 : rest.length + 6 < 1024 := by omega
  have hg7 : rest.length + 7 < 1024 := by omega
  have hg8 : rest.length + 8 < 1024 := by omega
  have hg9 : rest.length + 9 < 1024 := by omega
  have hg10 : rest.length + 10 < 1024 := by omega
  have hg11 : rest.length + 11 < 1024 := by omega
  have hg12 : rest.length + 12 < 1024 := by omega
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

      hcode, hrun, hpv, hsub, hactT, hactM,
      hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12,
      UInt256.gt, UInt256.lt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.ofNat_sub_ofNat, Nat.mod_eq_of_lt, List.exchange]

/-- `blk3157b` with limbs to go: pointer step and back to the inner loop head. -/
theorem run_addTail_go (s : State) (mm : ByteArray) (c p p' : UInt256)
    (n bsize esize msize k : Nat) (rest : List UInt256)
    (hp' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + p = p')
    (hcap : rest.length ≤ 1017)
    (hgt : 2111 < p'.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3157b
      { s with pc := UInt256.ofNat pcAddMid
               stack := p :: c :: UInt256.ofNat k :: rest
               memory := mm } =
      some { s with pc := UInt256.ofNat pcAddInner
                    stack := p' :: c :: UInt256.ofNat k :: rest
                    memory := mm } := by
  have hg3 : rest.length + 3 < 1024 := by omega
  have hg4 : rest.length + 4 < 1024 := by omega
  have hg5 : rest.length + 5 < 1024 := by omega
  have hg6 : rest.length + 6 < 1024 := by omega
  simp (config := { maxSteps := 200000 })
    [blk3157b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcAddMid, pcAddInner, hcode, hrun, hp', hgt, jumpDest5121, hg3, hg4, hg5, hg6,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]

/-- `blk3157b` after the last limb: pointer step and fall into the tail. -/
theorem run_addTail_last (s : State) (mm : ByteArray) (c p p' : UInt256)
    (n bsize esize msize k : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1017)
    (hp' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + p = p')
    (hle : p'.toNat = 2080)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3157b
      { s with pc := UInt256.ofNat pcAddMid
               stack := p :: c :: UInt256.ofNat k :: rest
               memory := mm } =
      some { s with pc := UInt256.ofNat pcAddPad
                    stack := p' :: c :: UInt256.ofNat k :: rest
                    memory := mm } := by
  have hg3 : rest.length + 3 < 1024 := by omega
  have hg4 : rest.length + 4 < 1024 := by omega
  have hg5 : rest.length + 5 < 1024 := by omega
  have hg6 : rest.length + 6 < 1024 := by omega
  simp (config := { maxSteps := 200000 })
    [blk3157b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcAddMid, pcAddPad, hcode, hrun, hp', hle, jumpDest5121, hg3, hg4, hg5, hg6,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]

/-- `blk3157c`: the five padding `JUMPDEST`s between the add exit test and the tail. -/
theorem run_addPad (s : State) (mm : ByteArray) (c p' : UInt256)
    (n bsize esize msize k : Nat) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3157c
      { s with pc := UInt256.ofNat pcAddPad
               stack := p' :: c :: UInt256.ofNat k :: rest
               memory := mm } =
      some { s with pc := UInt256.ofNat pcAddTail
                    stack := p' :: c :: UInt256.ofNat k :: rest
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3157c, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcAddPad, pcAddTail, hcode, hrun,
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
  have hslot : ∀ (v : Nat) (a : Nat), a + 32 ≤ 2080 →
      MachineState.readWord (MachineState.writeBytes (addStep mem n n).memory
        (Data.Bytes.natToBytesPadded v 32) 2080) a = MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 2080
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      addStep_readWord_disjoint mem n a (Or.inl (by omega)) n (Nat.le_refl n)]
  simp (config := { maxSteps := 300000 })
    [blk3192, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      addTailState, addLoopState, slotKState, rideSlots, entrySlots, shiftEntry, pcAddTail, pcAddLoop, addRoundMem, addCarry,
      Exp.storeWord, outer, Exp.outer, hcode, hrun, hTN, hc, jumpDest5115, hslot,
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
  have hslot : ∀ (v : Nat) (a : Nat), a + 32 ≤ 2080 →
      MachineState.readWord (MachineState.writeBytes (addStep mem n n).memory
        (Data.Bytes.natToBytesPadded v 32) 2080) a = MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 2080
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      addStep_readWord_disjoint mem n a (Or.inl (by omega)) n (Nat.le_refl n)]
  simp (config := { maxSteps := 300000 })
    [blk3192, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      addTailState, subCheckState, slotKState, rideSlots, entrySlots, shiftEntry,
      pcAddTail, pcSubCheck, addRoundMem, addCarry,
      Exp.storeWord, outer, Exp.outer, hcode, hrun, hTN, hc, jumpDest5115, hslot,
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
      subCheckState, csubCallState, slotKState, rideSlots, entrySlots, shiftEntry,
      pcSubCheck, pcCsubCall,
      outer, Exp.outer, hcode, hrun, hTN, htn, jumpDest5311, UInt256.isZero, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]




/-- `blk3253`: `k := k - 1` (`NOT ADD` on the zero above `k`), then jump STRAIGHT to the loop
head.  The `CSUB` call this block used to make is the identity on every reachable state
(`repair_lt_mm`), so the artifact no longer makes it. -/
theorem run_csubCall (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hk : 1 ≤ k) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3253
      (csubCallState s mem n bsize esize msize k) =
      some (afterCsubState s mem n bsize esize msize k) := by
  have hdec : UInt256.lnot (UInt256.ofNat 0) + UInt256.ofNat k =
      UInt256.ofNat (k - 1) := by
    interval_cases k <;> decide
  have hdec' : UInt256.lnot (0 : UInt256) + UInt256.ofNat k = UInt256.ofNat (k - 1) := hdec
  simp (config := { maxSteps := 200000 })
    [blk3253, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csubCallState, slotKState, rideSlots, entrySlots, shiftEntry, pcCsubCall, pcAfterCsub, afterCsubState,
      outer, Exp.outer, hcode, hrun, hdec, hdec', jumpDest4839,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `blk2764` (`E5`): with a word-sized exponent (`esize ≠ 1`) the squaring flag is
zero, the counter is the outer `n` itself, and the scratch slot takes the
unrolled-conversion entry `2899 + 133·[n = 4]`. -/
theorem run_e5 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hfast : n = 4 ∨ n = 8)
    (hact : 89 ≤ s.activeWords.toNat)
    (hesize : UInt256.ofNat esize ≠ UInt256.ofNat 1)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2764
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState s
        (Exp.storeWord (Exp.storeWord mem 1698 (shiftEntry n)) 1760 (UInt256.ofNat 0))
        n bsize esize msize n) := by
  have hne1 : ¬ (1 = esize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936) := by
    intro h
    apply hesize
    have hone : (1 : Nat) % 2 ^ 256 = 1 := Nat.mod_eq_of_lt (by norm_num)
    exact Challenge.EvmProof.Word.word_ext (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat, hone]
      exact h.symm)
  have he0 : UInt256.eq (UInt256.ofNat esize) (UInt256.ofNat 1) =
      UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]
    by_cases h : esize % 2 ^ 256 = 1 % 2 ^ 256
    · exact absurd (Challenge.EvmProof.Word.word_ext (by
          rw [Challenge.EvmProof.Word.word_toNat_ofNat,
            Challenge.EvmProof.Word.word_toNat_ofNat, h])) hesize
    · rw [if_neg h]
  have haw1698 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1698 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1760 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1760 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2816 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2816 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hv4 : (2899 + (UInt256.ofNat 133 * UInt256.ofNat 1).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 3032 := by
    have h : (UInt256.ofNat 133 * UInt256.ofNat 1).toNat = 133 := by decide
    rw [h]
  have hv8 : (2899 + (UInt256.ofNat 133 * UInt256.ofNat 0).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2899 := by
    have h : (UInt256.ofNat 133 * UInt256.ofNat 0).toNat = 0 := by decide
    rw [h]
  have hslot1698 : ∀ (v a : Nat), a + 32 ≤ 1698 →
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a =
        MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1698
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hslot1760 : ∀ (v a : Nat), a + 32 ≤ 1760 →
      MachineState.readWord
        (MachineState.writeBytes (MachineState.writeBytes mem
          (Data.Bytes.natToBytesPadded v 32) 1698) (Data.Bytes.natToBytesPadded 0 32) 1760) a =
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hback3032 : MachineState.readWord
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 3032 32) 1698)
        (Data.Bytes.natToBytesPadded 0 32) 1760) 1698 = UInt256.ofNat 3032 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 3032 (by decide)]
  have hback2899 : MachineState.readWord
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 2899 32) 1698)
        (Data.Bytes.natToBytesPadded 0 32) 1760) 1698 = UInt256.ofNat 2899 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 2899 (by decide)]
  have hz1 : (if 1 = esize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 then
        UInt256.ofNat 1 else UInt256.ofNat 0) = UInt256.ofNat 0 := by
    rw [if_neg hne1]
  rcases hfast with h | h <;> subst h <;>
    simp (config := { maxSteps := 3000000 })
    [blk2764, opAt, pushAt, wfOp, he0, hz1,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cacheSetupState, slotState, slotKState, shiftLoopState, rideSlots, entrySlots,
      shiftEntry, Exp.storeWord, outer, Exp.outer, hcode, hrun, pcShiftLoop,
      UInt256.eq, UInt256.isTrue, UInt256.land,
      haw1698, haw1760, haw2816, hv4, hv8, hslot1698, hslot1760, hback3032, hback2899,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]
  all_goals (simp only [State.activeWordsAfterUInt256, haw1698, haw1760, haw2816,
      hslot1698, hslot1760, hback3032, hback2899, hv4, hv8,
      Fin.land, Nat.and_zero, Nat.zero_and])
  all_goals (first | rfl | simp [UInt256.ofNat, UInt256.size, Fin.ofNat, Fin.land,
      Nat.and_zero, Nat.zero_and, UInt256.toNat, hback3032, hback2899])
  all_goals (first | rfl | decide)

/-- `blk2764` (`E5`), E3 arm: a one-byte exponent equal to `3` on a 4/8-limb
width sets the squaring flag and halves the loop counter. -/
theorem run_e5_e3 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hfast : n = 4 ∨ n = 8)
    (hact : 89 ≤ s.activeWords.toNat)
    (hsize1 : UInt256.ofNat esize = UInt256.ofNat 1)
    (hbyte3 : UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2816).toNat) =
      UInt256.ofNat 3)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2764
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState s
        (Exp.storeWord (Exp.storeWord mem 1698 (shiftEntry n)) 1760 (UInt256.ofNat 1))
        n bsize esize msize (n / 2)) := by
  have haw1698 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1698 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1760 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1760 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2816 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2816 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hmod : esize % 2 ^ 256 = 1 % 2 ^ 256 := by
    have h := congrArg UInt256.toNat hsize1
    rwa [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat] at h
  have hmodif : (if 1 = esize % 2 ^ 256 then UInt256.ofNat 1 else UInt256.ofNat 0) =
      UInt256.ofNat 1 := by
    rw [if_pos (by rw [hmod]; simp)]
  have he1 : UInt256.eq (UInt256.ofNat esize) (UInt256.ofNat 1) =
      UInt256.ofNat 1 := by
    unfold UInt256.eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat]
    rw [if_pos hmod]
  have hb3 : UInt256.eq (UInt256.ofNat 3)
      (UInt256.byteAt (UInt256.ofNat 0)
        (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2816).toNat)) =
      UInt256.ofNat 1 := by
    rw [hbyte3]
    unfold UInt256.eq
    simp
  have hb3t : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2816).toNat) =
      UInt256.ofNat 3 :=
    hbyte3
  have hb3m : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2816).val.val) =
      UInt256.ofNat 3 :=
    hbyte3
  have hmodl : esize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 1 := by
    rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 :
        Nat) = 2 ^ 256 from rfl, hmod]
    rfl
  have hv4 : (2899 + (UInt256.ofNat 133 * UInt256.ofNat 1).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 3032 := by
    have h : (UInt256.ofNat 133 * UInt256.ofNat 1).toNat = 133 := by decide
    rw [h]
  have hv8 : (2899 + (UInt256.ofNat 133 * UInt256.ofNat 0).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2899 := by
    have h : (UInt256.ofNat 133 * UInt256.ofNat 0).toNat = 0 := by decide
    rw [h]
  have hslot1698 : ∀ (v a : Nat), a + 32 ≤ 1698 →
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a =
        MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1698
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hhi1698 : ∀ (v a : Nat), 1698 + 32 ≤ a →
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a =
        MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1698
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hslot1760 : ∀ (v a : Nat), a + 32 ≤ 1760 →
      MachineState.readWord
        (MachineState.writeBytes (MachineState.writeBytes mem
          (Data.Bytes.natToBytesPadded v 32) 1698) (Data.Bytes.natToBytesPadded 1 32) 1760) a =
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hback3032 : MachineState.readWord
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 3032 32) 1698)
        (Data.Bytes.natToBytesPadded 1 32) 1760) 1698 = UInt256.ofNat 3032 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 3032 (by decide)]
  have hback2899 : MachineState.readWord
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 2899 32) 1698)
        (Data.Bytes.natToBytesPadded 1 32) 1760) 1698 = UInt256.ofNat 2899 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 2899 (by decide)]
  rcases hfast with h | h <;> subst h <;>
    simp (config := { maxSteps := 3000000 })
    [blk2764, opAt, pushAt, wfOp, he1, hb3,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cacheSetupState, slotState, slotKState, shiftLoopState, rideSlots, entrySlots,
      shiftEntry, Exp.storeWord, outer, Exp.outer, hcode, hrun, pcShiftLoop,
      UInt256.eq, UInt256.isTrue, UInt256.land, UInt256.isZero,
      haw1698, haw1760, haw2816, hv4, hv8, hslot1698, hhi1698, hslot1760, hback3032, hback2899,
      hmodif, hb3t, hb3m, hmodl,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]
  all_goals (simp only [State.activeWordsAfterUInt256, haw1698, haw1760, haw2816,
      hslot1698, hhi1698, hslot1760, hback3032, hback2899, hv4, hmodif, hmodl, hb3m,
      Fin.land, Nat.and_zero, Nat.zero_and])
  all_goals (first | rfl | simp [UInt256.ofNat, UInt256.size, Fin.ofNat, Fin.land,
      Nat.and_zero, Nat.zero_and, UInt256.toNat, hback3032, hback2899, hmodif, hmodl, hb3m])
  all_goals (first | rfl | decide)

/-- `blk2764` (`E5`), slow-exponent arm: a one-byte exponent whose single byte
is not `3` leaves the squaring flag at zero and the loop counter at `n`. -/
theorem run_e5_slowexp (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hfast : n = 4 ∨ n = 8)
    (hact : 89 ≤ s.activeWords.toNat)
    (hsize1 : UInt256.ofNat esize = UInt256.ofNat 1)
    (hbyteNe : UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2816).toNat) ≠
      UInt256.ofNat 3)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2764
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState s
        (Exp.storeWord (Exp.storeWord mem 1698 (shiftEntry n)) 1760 (UInt256.ofNat 0))
        n bsize esize msize n) := by
  have haw1698 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1698 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1760 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1760 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2816 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2816 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hmod : esize % 2 ^ 256 = 1 % 2 ^ 256 := by
    have h := congrArg UInt256.toNat hsize1
    rwa [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat] at h
  have hmodl : esize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 1 := by
    rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936:
        Nat) = 2 ^ 256 from rfl, hmod]
    rfl
  have hmodif : (if 1 = esize % 2 ^ 256 then UInt256.ofNat 1 else UInt256.ofNat 0) =
      UInt256.ofNat 1 := by
    rw [if_pos (by rw [hmod]; simp)]
  have he1 : UInt256.eq (UInt256.ofNat esize) (UInt256.ofNat 1) =
      UInt256.ofNat 1 := by
    unfold UInt256.eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat]
    rw [if_pos hmod]
  have hb3tne : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2816).toNat) ≠
      UInt256.ofNat 3 := hbyteNe
  have hb3mne : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2816).val.val) ≠
      UInt256.ofNat 3 := hbyteNe
  have hthree256 : (3 : Nat) % 2 ^ 256 = 3 := Nat.mod_eq_of_lt (by norm_num)
  have hbnT : ¬ (3 = (UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord mem 2816).toNat)).toNat) := by
    intro h
    apply hbyteNe
    refine Challenge.EvmProof.Word.word_ext ?_
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, hthree256]
    exact h.symm
  have hbn : ¬ (3 = (UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord mem 2816).val.val)).toNat) := by
    intro h
    apply hbyteNe
    refine Challenge.EvmProof.Word.word_ext ?_
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, hthree256]
    exact h.symm
  have hbn2 : ¬ (3 = ((UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord mem 2816).val.val)).val).val) := by
    intro h
    apply hbyteNe
    refine Challenge.EvmProof.Word.word_ext ?_
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, hthree256]
    exact h.symm
  have hv4 : (2899 + (UInt256.ofNat 133 * UInt256.ofNat 1).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 3032 := by
    have h : (UInt256.ofNat 133 * UInt256.ofNat 1).toNat = 133 := by decide
    rw [h]
  have hv8 : (2899 + (UInt256.ofNat 133 * UInt256.ofNat 0).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2899 := by
    have h : (UInt256.ofNat 133 * UInt256.ofNat 0).toNat = 0 := by decide
    rw [h]
  have hslot1698 : ∀ (v a : Nat), a + 32 ≤ 1698 →
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a =
        MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1698
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hhi1698 : ∀ (v a : Nat), 1698 + 32 ≤ a →
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a =
        MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1698
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hslot1760 : ∀ (v a : Nat), a + 32 ≤ 1760 →
      MachineState.readWord
        (MachineState.writeBytes (MachineState.writeBytes mem
          (Data.Bytes.natToBytesPadded v 32) 1698) (Data.Bytes.natToBytesPadded 0 32) 1760) a =
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hback3032 : MachineState.readWord
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 3032 32) 1698)
        (Data.Bytes.natToBytesPadded 0 32) 1760) 1698 = UInt256.ofNat 3032 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 3032 (by decide)]
  have hback2899 : MachineState.readWord
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 2899 32) 1698)
        (Data.Bytes.natToBytesPadded 0 32) 1760) 1698 = UInt256.ofNat 2899 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 2899 (by decide)]
  rcases hfast with h | h <;> subst h <;>
    simp (config := { maxSteps := 3000000 })
    [blk2764, opAt, pushAt, wfOp, he1, hb3tne, hb3mne, hbnT, hbn, hbn2,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cacheSetupState, slotState, slotKState, shiftLoopState, rideSlots, entrySlots,
      shiftEntry, Exp.storeWord, outer, Exp.outer, hcode, hrun, pcShiftLoop,
      UInt256.eq, UInt256.isTrue, UInt256.land, UInt256.isZero,
      haw1698, haw1760, haw2816, hv4, hv8, hslot1698, hhi1698, hslot1760, hback3032, hback2899,
      hmodif, hmodl,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]
  all_goals (simp only [State.activeWordsAfterUInt256, haw1698, haw1760, haw2816,
      hslot1698, hhi1698, hslot1760, hback3032, hback2899, hv4, hmodif, hmodl, hbn, hbn2,
      Fin.land, Nat.and_zero, Nat.zero_and])
  all_goals (first | rfl | simp [UInt256.ofNat, UInt256.size, Fin.ofNat, Fin.land,
      Nat.and_zero, Nat.zero_and, UInt256.toNat, hback3032, hback2899, hmodif, hmodl, hbn, hbn2,
      hb3mne])
  all_goals (first | rfl | decide)
@[simp] private theorem pcFact2700 :
    Artifact.submissionArtifact.instructionPC 2700 = 3352 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem pcFact4392 :
    Artifact.submissionArtifact.instructionPC 4392 = 5444 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- Followup-PC facts for the shift-done, cleanup and stub blocks. -/
@[simp] private theorem pc2701 : Artifact.submissionArtifact.instructionPC 2701 = 3353 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2702 : Artifact.submissionArtifact.instructionPC 2702 = 3356 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2703 : Artifact.submissionArtifact.instructionPC 2703 = 3357 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2704 : Artifact.submissionArtifact.instructionPC 2704 = 3358 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2705 : Artifact.submissionArtifact.instructionPC 2705 = 3361 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2706 : Artifact.submissionArtifact.instructionPC 2706 = 3362 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2707 : Artifact.submissionArtifact.instructionPC 2707 = 3363 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2708 : Artifact.submissionArtifact.instructionPC 2708 = 3366 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2709 : Artifact.submissionArtifact.instructionPC 2709 = 3369 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2710 : Artifact.submissionArtifact.instructionPC 2710 = 3370 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2711 : Artifact.submissionArtifact.instructionPC 2711 = 3371 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2712 : Artifact.submissionArtifact.instructionPC 2712 = 3373 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2713 : Artifact.submissionArtifact.instructionPC 2713 = 3374 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2714 : Artifact.submissionArtifact.instructionPC 2714 = 3377 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc2715 : Artifact.submissionArtifact.instructionPC 2715 = 3378 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4393 : Artifact.submissionArtifact.instructionPC 4393 = 5445 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4394 : Artifact.submissionArtifact.instructionPC 4394 = 5446 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4395 : Artifact.submissionArtifact.instructionPC 4395 = 5447 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4396 : Artifact.submissionArtifact.instructionPC 4396 = 5448 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4397 : Artifact.submissionArtifact.instructionPC 4397 = 5449 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4398 : Artifact.submissionArtifact.instructionPC 4398 = 5450 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4399 : Artifact.submissionArtifact.instructionPC 4399 = 5451 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4400 : Artifact.submissionArtifact.instructionPC 4400 = 5452 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4403 : Artifact.submissionArtifact.instructionPC 4403 = 5455 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl

@[simp] private theorem pc4402 : Artifact.submissionArtifact.instructionPC 4402 = 5454 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl

@[simp] private theorem pc4401 : Artifact.submissionArtifact.instructionPC 4401 = 5453 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4404 : Artifact.submissionArtifact.instructionPC 4404 = 5456 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4405 : Artifact.submissionArtifact.instructionPC 4405 = 5457 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4406 : Artifact.submissionArtifact.instructionPC 4406 = 5458 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4407 : Artifact.submissionArtifact.instructionPC 4407 = 5459 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4408 : Artifact.submissionArtifact.instructionPC 4408 = 5460 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4409 : Artifact.submissionArtifact.instructionPC 4409 = 5461 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4410 : Artifact.submissionArtifact.instructionPC 4410 = 5462 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pc4411 : Artifact.submissionArtifact.instructionPC 4411 = 5465 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl

/-- `blk3346` with the squaring flag clear: drop the counter and jump to the
cleanup tail. -/
theorem run_shiftDone_check (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 89 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3346
      (shiftDoneState s mem n bsize esize msize) =
      some (cleanupState s mem n bsize esize msize) := by
  have hawSD1760 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1760 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk3346, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftDoneState, cleanupState, slotState, slotKState, rideSlots, entrySlots,
      shiftEntry, pcShiftDone, outer, Exp.outer, hcode, hrun, hflag, jumpDest5444, jumpDest3412,
      UInt256.isZero, UInt256.isTrue, hawSD1760,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk5444`: seventeen `POP`s drop the riding slots and jump to the done stub. -/
theorem run_cleanup (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk5444
      (cleanupState s mem n bsize esize msize) =
      some (postCleanupState s mem n bsize esize msize) := by
  simp (config := { maxSteps := 3000000 })
    [blk5444, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cleanupState, postCleanupState, slotState, frameState, rideSlots, entrySlots,
      shiftEntry, outer, Exp.outer, hcode, hrun, jumpDest3378,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3378`: jump to the exponent dispatcher. -/
theorem run_bdoneStub (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3378
      (postCleanupState s mem n bsize esize msize) =
      some (frameState s mem 2441 n bsize esize msize) := by
  simp (config := { maxSteps := 200000 })

    [blk3378, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      postCleanupState, frameState, outer, Exp.outer, hcode, hrun, jumpDest3412,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.Shift
