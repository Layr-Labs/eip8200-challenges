import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftTrace2
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic
import Challenge.Modexp.Submission.Proofs.CycleGlobal.RetainedTEntry

noncomputable section
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Block reductions of the shift-reduce base conversion, part 3

The middle block, the two repair loops, the `CSUB` call and the loop exits.
-/

attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old1
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old2
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old3
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old3b
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old4
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old_tail5
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old_tail6
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old_tail7
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old_tail8
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old_tail10
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old_tail11
attribute [-simp] CycleSubmission.Global.PrefixPC.eq_old_tail12

namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift


attribute [local simp] CompactConstants.notThirtyOne notThirtyOneOfNat

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open CycleSubmission.Global.ShiftPCs

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
theorem run_mid_unc (z : UInt256) (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hn32 : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hor : (negOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q).toNat ≠ 0 ∨ (tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q).toNat ≠ 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3125
      (midState z s um q n bsize esize msize k) =
      some (uncState z s (midMem (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) n bsize esize msize k
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
theorem run_mid_zero (z : UInt256) (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hn32 : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hneg : negOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q = UInt256.ofNat 0)
    (htz : tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3125
      (midState z s um q n bsize esize msize k) =
      some (csubCallState z s (midMem (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) n bsize esize msize k) := by
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

theorem pcUncPop : CycleSubmission.Artifact.artifact.instructionPC 2391 = 3105 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- `UNC` with `neg ≠ 0`: fall into `ADD_LOOP`. -/
theorem run_unc_add (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) (f : UInt256)
    (hf : f.toNat ≠ 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkUnc
      (uncState z s mem n bsize esize msize k f) =
      some (addLoopState z s mem n bsize esize msize k) := by
  simp (config := { maxSteps := 200000 })
    [blkUnc, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      uncState, addLoopState, slotKState, rideSlots, entrySlots, shiftEntry, pcUnc, pcAddLoop,
      outer, Exp.outer, hcode, hrun, hf, pcUncPop, UInt256.isZero, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]


/-- `blk3153`: the add round's frame `[p, 0, k]`. -/
theorem run_addEntry (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3153
      (addLoopState z s mem n bsize esize msize k) =
      some (addInnerState z s mem n bsize esize msize k 0) := by
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
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
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
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
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
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
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
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
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
theorem run_addTail_again (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hout : addOut mem n = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3192
      (addTailState z s mem n bsize esize msize k) =
      some (addLoopState z s (addRoundMem mem n) n bsize esize msize k) := by
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
theorem run_addTail_done (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hout : addOut mem n = UInt256.ofNat 1)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3192
      (addTailState z s mem n bsize esize msize k) =
      some (subCheckState z s (addRoundMem mem n) n bsize esize msize k) := by
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
theorem run_subCheck_done (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (htn : (MachineState.readWord mem 2080).toNat = 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3204
      (subCheckState z s mem n bsize esize msize k) =
      some (csubCallState z s mem n bsize esize msize k) := by
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




/-- `blk3253`: `k := k - 1` (`NOT ADD` on the zero above `k`), then back to the loop head while
`k - 1 ≠ 0`.  The `CSUB` call this block used to make is the identity on every reachable state
(`repair_lt_mm`), so the artifact no longer makes it. -/
theorem run_csubCall (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hk : 2 ≤ k) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3253
      (csubCallState z s mem n bsize esize msize k) =
      some (afterCsubState z s mem n bsize esize msize k) := by
  have hdec : UInt256.lnot (UInt256.ofNat 0) + UInt256.ofNat k =
      UInt256.ofNat (k - 1) := by
    interval_cases k <;> decide
  have hdec' : UInt256.lnot (0 : UInt256) + UInt256.ofNat k = UInt256.ofNat (k - 1) := hdec
  have htrue : UInt256.isTrue (UInt256.ofNat (k - 1)) := by
    show (UInt256.ofNat (k - 1)).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 200000 })
    [blk3253, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csubCallState, slotKState, rideSlots, entrySlots, shiftEntry, pcCsubCall, pcAfterCsub, afterCsubState,
      outer, Exp.outer, hcode, hrun, hdec, hdec', htrue, jumpDest4839,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `blk3253` on the last step: the counter reaches zero and the `JUMPI` falls through. -/
theorem run_csubCall_last (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3253
      (csubCallState z s mem n bsize esize msize 1) =
      some (csubExitState z s mem n bsize esize msize) := by
  have hdec : UInt256.lnot (UInt256.ofNat 0) + UInt256.ofNat 1 = UInt256.ofNat 0 := by decide
  have hdec' : UInt256.lnot (0 : UInt256) + UInt256.ofNat 1 = UInt256.ofNat 0 := hdec
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 200000 })
    [blk3253, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csubCallState, slotKState, rideSlots, entrySlots, shiftEntry, pcCsubCall, pcCsubExit,
      csubExitState,
      outer, Exp.outer, hrun, hdec, hdec', hfalse,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `blk3253x`: the loop exit jumps to `SHIFT_DONE`. -/
theorem run_csubExit (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3253x
      (csubExitState z s mem n bsize esize msize) =
      some (shiftDoneState z s mem n bsize esize msize) := by
  simp (config := { maxSteps := 200000 })
    [blk3253x, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csubExitState, shiftDoneState, slotKState, rideSlots, entrySlots, shiftEntry,
      pcCsubExit, pcShiftDone,
      outer, Exp.outer, hcode, hrun, jumpDest5366,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk2764` (`E5`): with a word-sized exponent (`esize ≠ 1`) the squaring flag is
zero, the counter is the outer `n` itself, and the scratch slot takes the
unrolled-conversion entry `2940 + 116·[n = 4]`. -/
theorem run_e5 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hfast : n = 4 ∨ n = 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hesize : UInt256.ofNat esize ≠ UInt256.ofNat 1)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2764
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState (UInt256.ofNat 0) s
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
  have haw2816 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2656 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hv4 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3048 -
      (UInt256.ofNat 29 * UInt256.ofNat 4).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2932 := by decide
  have hv8 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3048 -
      (UInt256.ofNat 29 * UInt256.ofNat 8).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2816 := by decide
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
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 2932 32) 1698)
        (Data.Bytes.natToBytesPadded 0 32) 1760) 1698 = UInt256.ofNat 2932 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 2932 (by decide)]
  have hback2899 : MachineState.readWord
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 2816 32) 1698)
        (Data.Bytes.natToBytesPadded 0 32) 1760) 1698 = UInt256.ofNat 2816 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 2816 (by decide)]
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
    (hact : 88 ≤ s.activeWords.toNat)
    (hsize1 : UInt256.ofNat esize = UInt256.ofNat 1)
    (hbyte3 : UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat) =
      UInt256.ofNat 3)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2764
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState (UInt256.ofNat 0) s
        (Exp.storeWord (Exp.storeWord mem 1698 (shiftEntry n)) 1760 (UInt256.ofNat 1))
        n bsize esize msize (n / 2)) := by
  have haw1698 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1698 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1760 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1760 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2816 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2656 32) =
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
        (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat)) =
      UInt256.ofNat 1 := by
    rw [hbyte3]
    unfold UInt256.eq
    simp
  have hb3t : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat) =
      UInt256.ofNat 3 :=
    hbyte3
  have hb3m : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).val.val) =
      UInt256.ofNat 3 :=
    hbyte3
  have hmodl : esize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 1 := by
    rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 :
        Nat) = 2 ^ 256 from rfl, hmod]
    rfl
  have hv4 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3048 -
      (UInt256.ofNat 29 * UInt256.ofNat 4).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2932 := by decide
  have hv8 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3048 -
      (UInt256.ofNat 29 * UInt256.ofNat 8).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2816 := by decide
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
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 2932 32) 1698)
        (Data.Bytes.natToBytesPadded 1 32) 1760) 1698 = UInt256.ofNat 2932 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 2932 (by decide)]
  have hback2899 : MachineState.readWord
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 2816 32) 1698)
        (Data.Bytes.natToBytesPadded 1 32) 1760) 1698 = UInt256.ofNat 2816 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 2816 (by decide)]
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
    (hact : 88 ≤ s.activeWords.toNat)
    (hsize1 : UInt256.ofNat esize = UInt256.ofNat 1)
    (hbyteNe : UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat) ≠
      UInt256.ofNat 3)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2764
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState (UInt256.ofNat 0) s
        (Exp.storeWord (Exp.storeWord mem 1698 (shiftEntry n)) 1760 (UInt256.ofNat 0))
        n bsize esize msize n) := by
  have haw1698 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1698 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1760 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1760 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2816 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2656 32) =
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
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat) ≠
      UInt256.ofNat 3 := hbyteNe
  have hb3mne : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).val.val) ≠
      UInt256.ofNat 3 := hbyteNe
  have hthree256 : (3 : Nat) % 2 ^ 256 = 3 := Nat.mod_eq_of_lt (by norm_num)
  have hbnT : ¬ (3 = (UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord mem 2656).toNat)).toNat) := by
    intro h
    apply hbyteNe
    refine Challenge.EvmProof.Word.word_ext ?_
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, hthree256]
    exact h.symm
  have hbn : ¬ (3 = (UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord mem 2656).val.val)).toNat) := by
    intro h
    apply hbyteNe
    refine Challenge.EvmProof.Word.word_ext ?_
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, hthree256]
    exact h.symm
  have hbn2 : ¬ (3 = ((UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord mem 2656).val.val)).val).val) := by
    intro h
    apply hbyteNe
    refine Challenge.EvmProof.Word.word_ext ?_
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, hthree256]
    exact h.symm
  have hv4 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3048 -
      (UInt256.ofNat 29 * UInt256.ofNat 4).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2932 := by decide
  have hv8 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3048 -
      (UInt256.ofNat 29 * UInt256.ofNat 8).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2816 := by decide
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
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 2932 32) 1698)
        (Data.Bytes.natToBytesPadded 0 32) 1760) 1698 = UInt256.ofNat 2932 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 2932 (by decide)]
  have hback2899 : MachineState.readWord
      (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 2816 32) 1698)
        (Data.Bytes.natToBytesPadded 0 32) 1760) 1698 = UInt256.ofNat 2816 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ 1698 1760
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 1698 2816 (by decide)]
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
    CycleSubmission.Artifact.artifact.instructionPC 2448 = 3183 := by
  rw [show (2448:Nat)=2391+(2448-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl

@[simp] private theorem pcFact4392 :
    CycleSubmission.Artifact.artifact.instructionPC 3052 = 3944 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- Followup-PC facts for the shift-done, cleanup and stub blocks. -/
@[simp] private theorem pc2701 : CycleSubmission.Artifact.artifact.instructionPC 2449 = 3184 := by
  rw [show (2449:Nat)=2391+(2449-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2702 : CycleSubmission.Artifact.artifact.instructionPC 2450 = 3187 := by
  rw [show (2450:Nat)=2391+(2450-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2703 : CycleSubmission.Artifact.artifact.instructionPC 2451 = 3188 := by
  rw [show (2451:Nat)=2391+(2451-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2704 : CycleSubmission.Artifact.artifact.instructionPC 2452 = 3189 := by
  rw [show (2452:Nat)=2391+(2452-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2705 : CycleSubmission.Artifact.artifact.instructionPC 2453 = 3192 := by
  rw [show (2453:Nat)=2391+(2453-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2706 : CycleSubmission.Artifact.artifact.instructionPC 2466 = 3213 := by
  rw [show (2466:Nat)=2391+(2466-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2707 : CycleSubmission.Artifact.artifact.instructionPC 2455 = 3195 := by
  rw [show (2455:Nat)=2391+(2455-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2708 : CycleSubmission.Artifact.artifact.instructionPC 2456 = 3196 := by
  rw [show (2456:Nat)=2391+(2456-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2709 : CycleSubmission.Artifact.artifact.instructionPC 2457 = 3197 := by
  rw [show (2457:Nat)=2391+(2457-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2710 : CycleSubmission.Artifact.artifact.instructionPC 2458 = 3200 := by
  rw [show (2458:Nat)=2391+(2458-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2711 : CycleSubmission.Artifact.artifact.instructionPC 2459 = 3203 := by
  rw [show (2459:Nat)=2391+(2459-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2712 : CycleSubmission.Artifact.artifact.instructionPC 2460 = 3204 := by
  rw [show (2460:Nat)=2391+(2460-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2713 : CycleSubmission.Artifact.artifact.instructionPC 2461 = 3205 := by
  rw [show (2461:Nat)=2391+(2461-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2714 : CycleSubmission.Artifact.artifact.instructionPC 2462 = 3207 := by
  rw [show (2462:Nat)=2391+(2462-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc2715 : CycleSubmission.Artifact.artifact.instructionPC 2463 = 3208 := by
  rw [show (2463:Nat)=2391+(2463-2391) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcUncPop]
  rfl
@[simp] private theorem pc4393 : CycleSubmission.Artifact.artifact.instructionPC 3053 = 3945 := by
  rw [show (3053:Nat)=3052+(3053-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4394 : CycleSubmission.Artifact.artifact.instructionPC 3054 = 3946 := by
  rw [show (3054:Nat)=3052+(3054-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4395 : CycleSubmission.Artifact.artifact.instructionPC 3055 = 3947 := by
  rw [show (3055:Nat)=3052+(3055-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4396 : CycleSubmission.Artifact.artifact.instructionPC 3056 = 3948 := by
  rw [show (3056:Nat)=3052+(3056-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4397 : CycleSubmission.Artifact.artifact.instructionPC 3057 = 3949 := by
  rw [show (3057:Nat)=3052+(3057-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4398 : CycleSubmission.Artifact.artifact.instructionPC 3058 = 3950 := by
  rw [show (3058:Nat)=3052+(3058-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4399 : CycleSubmission.Artifact.artifact.instructionPC 3059 = 3951 := by
  rw [show (3059:Nat)=3052+(3059-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4400 : CycleSubmission.Artifact.artifact.instructionPC 3060 = 3952 := by
  rw [show (3060:Nat)=3052+(3060-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4403 : CycleSubmission.Artifact.artifact.instructionPC 3063 = 3955 := by
  rw [show (3063:Nat)=3052+(3063-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl

@[simp] private theorem pc4402 : CycleSubmission.Artifact.artifact.instructionPC 3062 = 3954 := by
  rw [show (3062:Nat)=3052+(3062-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl

@[simp] private theorem pc4401 : CycleSubmission.Artifact.artifact.instructionPC 3061 = 3953 := by
  rw [show (3061:Nat)=3052+(3061-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4404 : CycleSubmission.Artifact.artifact.instructionPC 3064 = 3956 := by
  rw [show (3064:Nat)=3052+(3064-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4405 : CycleSubmission.Artifact.artifact.instructionPC 3065 = 3957 := by
  rw [show (3065:Nat)=3052+(3065-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4406 : CycleSubmission.Artifact.artifact.instructionPC 3066 = 3958 := by
  rw [show (3066:Nat)=3052+(3066-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4407 : CycleSubmission.Artifact.artifact.instructionPC 3067 = 3959 := by
  rw [show (3067:Nat)=3052+(3067-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4408 : CycleSubmission.Artifact.artifact.instructionPC 3068 = 3960 := by
  rw [show (3068:Nat)=3052+(3068-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4409 : CycleSubmission.Artifact.artifact.instructionPC 3069 = 3961 := by
  rw [show (3069:Nat)=3052+(3069-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4410 : CycleSubmission.Artifact.artifact.instructionPC 3070 = 3964 := by
  rw [show (3070:Nat)=3052+(3070-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl
@[simp] private theorem pc4411 : CycleSubmission.Artifact.artifact.instructionPC 3071 = 3965 := by
  rw [show (3071:Nat)=3052+(3071-3052) from rfl, CycleSubmission.Global.PrefixPC.pc_add, pcFact4392]
  rfl

/-- `blk3346` with the squaring flag clear: drop the counter and jump to the
cleanup tail. -/
theorem run_shiftDone_check (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3346
      (shiftDoneState z s mem n bsize esize msize) =
      some (cleanupState z s mem n bsize esize msize) := by
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

/-- `blk5444`: sixteen `POP`s leave the exit slot `z = d` above the outer frame, and
`PUSH2 0989 ADD JUMP` jumps to `2441 + d`: the exponent dispatcher for `d = 0` (`E5`'s slot)
and `e3go` at 2471 for `d = 28` (set by the E3 phase switch). -/
theorem run_cleanup (s : State) (mem : ByteArray) (n bsize esize msize d target : Nat)
    (htarget : 2317 + d = target) (hlt : target < 2 ^ 256)
    (hdest : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode target = true)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk5444
      (cleanupState (UInt256.ofNat d) s mem n bsize esize msize) =
      some (frameState s mem target n bsize esize msize) := by
  have hadd : UInt256.ofNat 2317 + UInt256.ofNat d = UInt256.ofNat target := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod, htarget]
  have hmod : target %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = target :=
    Nat.mod_eq_of_lt hlt
  have hmod' : target % 2 ^ 256 = target := Nat.mod_eq_of_lt hlt
  simp (config := { maxSteps := 3000000 })
    [blk5444, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cleanupState, slotState, frameState, rideSlots, entrySlots,
      shiftEntry, outer, Exp.outer, hcode, hrun, hadd, htarget, hmod, hmod', hdest,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

end CycleSubmission.Global.Fast.Shift
