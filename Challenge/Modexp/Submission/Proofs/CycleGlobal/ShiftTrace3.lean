import Challenge.Modexp.Submission.Proofs.CycleGlobal.DifferenceBranch
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
# Block reductions of the shift-reduce base conversion,part 3

The middle block,the two repair loops,the `CSUB` call and the loop exits.
-/


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
(`[s,c,q]` ↦ `GT c s`,`GT q s`); rewriting every `GT` to `LT` puts the
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


/-- Store TN and enter UNC with a disposable MAX word. The mathematical negative flag remains in the hypothesis,but the repair entry immediately pops its runtime word. -/
theorem run_mid_unc (z : UInt256) (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hw : n ≠ 4)
    (hn32 : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hor : (negOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q).toNat ≠ 0 ∨ (tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q).toNat ≠ 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3125Unc
      (midState z s um q n bsize esize msize k) =
      some (uncState z s (midMem (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) n bsize esize msize k
        Monpro.maxWord) := by
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hslot : ∀ (v : Nat) (a : Nat),a + 32 ≤ 2048 →
      MachineState.readWord (MachineState.writeBytes (Monpro.l1Step um q NEG n n).memory
        (Data.Bytes.natToBytesPadded v 32) 2080) a = MachineState.readWord um a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 2080
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Monpro.readWord_l1Step um q NEG n a n hn32 (Or.inl ha)]
  have htnTrue : UInt256.isTrue (tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) := by
    exact CycleSubmission.DifferenceBranch.difference_nonzero_of_flags
      (wN (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry) q (cwOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry) hor
  unfold tnOf wN at htnTrue
  have hA : MachineState.readWord (Monpro.l1Step um q NEG n n).memory 2080 +
      (Monpro.l1Step um q NEG n n).carry =
      (Monpro.l1Step um q NEG n n).carry + MachineState.readWord (Monpro.l1Step um q NEG n n).memory 2080 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp (config := { maxSteps := 500000 })
    [blk3125Unc,hA,midGtSwap,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      midState,midPC,hw,uncState,pcMid,pcUnc,midMem,negOf,bwOf,cwOf,tnOf,wN,Exp.storeWord,
      outer,Exp.outer,hcode,hrun,hTN,htnTrue,jumpDestUnc,
      hslot,entrySlots,rideSlots,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange]
  all_goals constructor <;> rfl


theorem run_mid_unc_h4 (z : UInt256) (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hn32 : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hor : (negOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q).toNat ≠ 0 ∨ (tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q).toNat ≠ 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3125hUnc
      (midState z s um q n bsize esize msize k) =
      some (uncState z s (midMem (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) n bsize esize msize k
        Monpro.maxWord) := by
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hslot : ∀ (v : Nat) (a : Nat),a + 32 ≤ 2048 →
      MachineState.readWord (MachineState.writeBytes (Monpro.l1Step um q NEG n n).memory
        (Data.Bytes.natToBytesPadded v 32) 2080) a = MachineState.readWord um a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 2080
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      Monpro.readWord_l1Step um q NEG n a n hn32 (Or.inl ha)]
  have htnTrue : UInt256.isTrue (tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) := by
    exact CycleSubmission.DifferenceBranch.difference_nonzero_of_flags
      (wN (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry) q (cwOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry) hor
  unfold tnOf wN at htnTrue
  have hpc : midPC n = 10907 := by simp [midPC,hw]
  have hA : MachineState.readWord (Monpro.l1Step um q NEG n n).memory 2080 +
      (Monpro.l1Step um q NEG n n).carry =
      (Monpro.l1Step um q NEG n n).carry + MachineState.readWord (Monpro.l1Step um q NEG n n).memory 2080 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp (config := { maxSteps := 500000 })
    [blk3125hUnc,hA,midGtSwap,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      midState,hpc,uncState,pcMid,pcUnc,midMem,negOf,bwOf,cwOf,tnOf,wN,Exp.storeWord,
      outer,Exp.outer,hcode,hrun,hTN,htnTrue,jumpDestUnc,
      hslot,entrySlots,rideSlots,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange]
  all_goals constructor <;> rfl

/-- `blk3125` with `neg = 0` and `TN = 0`: fall into the `CSUB` call with `[0,k]`. -/
theorem run_mid_zero (z : UInt256) (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hw : n ≠ 4)
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
  have hslot : ∀ (v : Nat) (a : Nat),a + 32 ≤ 2048 →
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
  have hA : MachineState.readWord (Monpro.l1Step um q NEG n n).memory 2080 +
      (Monpro.l1Step um q NEG n n).carry =
      (Monpro.l1Step um q NEG n n).carry + MachineState.readWord (Monpro.l1Step um q NEG n n).memory 2080 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp (config := { maxSteps := 1500000 })
    [blk3125,hA,Monpro.maxWord,midGtSwap,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      midState,midPC,hw,csubCallState,pcMid,pcCsubCall,Exp.storeWord,entrySlots,rideSlots,
      outer,Exp.outer,hcode,hrun,hTN,hneg,htz,hz,hz1,hz2,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      hslot,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange]
  all_goals rfl


theorem run_mid_zero_h4 (z : UInt256) (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hn32 : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hneg : negOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q = UInt256.ofNat 0)
    (htz : tnOf (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q = UInt256.ofNat 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3125h
      (midState z s um q n bsize esize msize k) =
      some (csubCall4State z s (midMem (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q) n bsize esize msize k) := by
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hz : ¬ UInt256.isTrue (UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0)) := by decide
  have hz1 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
  have hz2 : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hmem : midMem (Monpro.l1Step um q NEG n n).memory (Monpro.l1Step um q NEG n n).carry q = Exp.storeWord (Monpro.l1Step um q NEG n n).memory 2080 (UInt256.ofNat 0) := by
    unfold midMem; rw [htz]
  have hslot : ∀ (v : Nat) (a : Nat),a + 32 ≤ 2048 →
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
  have hpc : midPC n = 10907 := by simp [midPC,hw]
  have hA : MachineState.readWord (Monpro.l1Step um q NEG n n).memory 2080 +
      (Monpro.l1Step um q NEG n n).carry =
      (Monpro.l1Step um q NEG n n).carry + MachineState.readWord (Monpro.l1Step um q NEG n n).memory 2080 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp (config := { maxSteps := 1500000 })
    [blk3125h,hA,Monpro.maxWord,midGtSwap,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      midState,hpc,csubCall4State,pcMid,Exp.storeWord,entrySlots,rideSlots,
      outer,Exp.outer,hcode,hrun,hTN,hneg,htz,hz,hz1,hz2,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      hslot,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange]
  all_goals rfl

@[simp] theorem pcUncPop : CycleSubmission.Artifact.artifact.instructionPC 2340 = 3053 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- The repair entry discards its carried word; its value is irrelevant to ADD_LOOP. -/
theorem run_unc_add (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) (f : UInt256)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkUnc
      (uncState z s mem n bsize esize msize k f) =
      some (addLoopState z s mem n bsize esize msize k) := by
  simp (config := { maxSteps := 200000 })
    [blkUnc,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      uncState,addLoopState,slotKState,rideSlots,entrySlots,shiftEntry,pcUnc,pcAddLoop,
      outer,Exp.outer,hcode,hrun,pcUncPop,UInt256.isZero,UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange]


/-- `blk3153`: the add round's frame `[p,0,k]`. -/
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
    [blk3153,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      addLoopState,addInnerState,slotKState,rideSlots,entrySlots,shiftEntry,pcAddLoop,pcAddInner,addStep,
      outer,Exp.outer,hcode,hrun,htl,hTL,Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3157a`: one limb of the add pass,up to `OR`,with the loop pointer
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
    [blk3157a,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcAddInner,pcAddMid,addStep,

      hcode,hrun,hpv,hsub,hactT,hactM,
      hg3,hg4,hg5,hg6,hg7,hg8,hg9,hg10,hg11,hg12,
      UInt256.gt,UInt256.lt,UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.ofNat_sub_ofNat,Nat.mod_eq_of_lt,List.exchange]

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
    [blk3157b,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcAddMid,pcAddInner,hcode,hrun,hp',hgt,jumpDest5121,hg3,hg4,hg5,hg6,
      UInt256.gt,UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,Nat.mod_eq_of_lt,List.exchange]

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
    [blk3157b,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcAddMid,pcAddPad,hcode,hrun,hp',hle,jumpDest5121,hg3,hg4,hg5,hg6,
      UInt256.gt,UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,Nat.mod_eq_of_lt,List.exchange]

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
    [blk3157c,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcAddPad,pcAddTail,hcode,hrun,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,Nat.mod_eq_of_lt,List.exchange]

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
  have hslot : ∀ (v : Nat) (a : Nat),a + 32 ≤ 2080 →
      MachineState.readWord (MachineState.writeBytes (addStep mem n n).memory
        (Data.Bytes.natToBytesPadded v 32) 2080) a = MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 2080
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      addStep_readWord_disjoint mem n a (Or.inl (by omega)) n (Nat.le_refl n)]
  simp (config := { maxSteps := 300000 })
    [blk3192,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      addTailState,addLoopState,slotKState,rideSlots,entrySlots,shiftEntry,pcAddTail,pcAddLoop,addRoundMem,addCarry,
      Exp.storeWord,outer,Exp.outer,hcode,hrun,hTN,hc,jumpDest5115,hslot,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3192` with a carry out of `TN`: the value is non-negative,go to `SUB_CHECK`. -/
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
  have hslot : ∀ (v : Nat) (a : Nat),a + 32 ≤ 2080 →
      MachineState.readWord (MachineState.writeBytes (addStep mem n n).memory
        (Data.Bytes.natToBytesPadded v 32) 2080) a = MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 2080
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      addStep_readWord_disjoint mem n a (Or.inl (by omega)) n (Nat.le_refl n)]
  simp (config := { maxSteps := 300000 })
    [blk3192,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      addTailState,subCheckState,slotKState,rideSlots,entrySlots,shiftEntry,
      pcAddTail,pcSubCheck,addRoundMem,addCarry,
      Exp.storeWord,outer,Exp.outer,hcode,hrun,hTN,hc,jumpDest5115,hslot,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3204` with `TN = 0`: jump to the `CSUB` call with `[TN,k]`. -/
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
    [blk3204,Monpro.maxWord,Exp.push0_word,opAt,pushAt,wfOp,htn0,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      subCheckState,csubCallState,slotKState,rideSlots,entrySlots,shiftEntry,
      pcSubCheck,pcCsubCall,
      outer,Exp.outer,hcode,hrun,hTN,htn,jumpDest5311,UInt256.isZero,UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  decide




/-- `blk3253`: `k := k - 1` (`NOT ADD` on the zero above `k`),then back to the loop head while
`k - 1 ≠ 0`.  The `CSUB` call this block used to make is the identity on every reachable state
(`repair_lt_mm`),so the artifact no longer makes it. -/
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
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have headPC_mod : headPC n %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = headPC n :=
    Nat.mod_eq_of_lt (by unfold headPC; split_ifs <;> norm_num)
  have hdecMax : Monpro.maxWord + UInt256.ofNat k = UInt256.ofNat (k - 1) := by
    rw [show Monpro.maxWord = UInt256.lnot (UInt256.ofNat 0) by decide]
    exact hdec
  simp (config := { maxSteps := 200000 })
    [blk3253,hdecMax,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csubCallState,slotKState,rideSlots,entrySlots,shiftEntry,pcCsubCall,pcAfterCsub,afterCsubState,
      outer,Exp.outer,hcode,hrun,hdec,hdec',htrue,headWord,headPC_mod,jumpDestHead,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange]


theorem run_csubCall_h4 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hk : 2 ≤ k) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3253h
      (csubCall4State z s mem n bsize esize msize k) =
      some (afterCsubState z s mem n bsize esize msize k) := by
  have hdec : UInt256.lnot (UInt256.ofNat 0) + UInt256.ofNat k =
      UInt256.ofNat (k - 1) := by
    interval_cases k <;> decide
  have hdec' : UInt256.lnot (0 : UInt256) + UInt256.ofNat k = UInt256.ofNat (k - 1) := hdec
  have htrue : UInt256.isTrue (UInt256.ofNat (k - 1)) := by
    show (UInt256.ofNat (k - 1)).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have headPC_mod : headPC n %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = headPC n :=
    Nat.mod_eq_of_lt (by unfold headPC; split_ifs <;> norm_num)
  have hdecMax : Monpro.maxWord + UInt256.ofNat k = UInt256.ofNat (k - 1) := by
    rw [show Monpro.maxWord = UInt256.lnot (UInt256.ofNat 0) by decide]
    exact hdec
  simp (config := { maxSteps := 200000 })
    [blk3253h,hdecMax,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csubCall4State,slotKState,rideSlots,entrySlots,shiftEntry,pcCsubCall,pcAfterCsub,afterCsubState,
      outer,Exp.outer,hcode,hrun,hdec,hdec',htrue,headWord,headPC_mod,jumpDestHead,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange]

/-- `blk3253` on the last step: the counter reaches zero and the `JUMPI` falls through. -/
theorem run_csubCall_last (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3253Last
      (csubCallState z s mem n bsize esize msize 1) =
      some (csubExitState z s mem n bsize esize msize) := by
  have hdec : UInt256.lnot (UInt256.ofNat 0) + UInt256.ofNat 1 = UInt256.ofNat 0 := by decide
  have hdec' : UInt256.lnot (0 : UInt256) + UInt256.ofNat 1 = UInt256.ofNat 0 := hdec
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hdecMax : Monpro.maxWord + UInt256.ofNat 1 = UInt256.ofNat 0 := by
    rw [show Monpro.maxWord = UInt256.lnot (UInt256.ofNat 0) by decide]
    exact hdec
  simp (config := { maxSteps := 200000 })
    [blk3253Last,hdecMax,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csubCallState,slotKState,rideSlots,entrySlots,shiftEntry,pcCsubCall,pcCsubExit,
      csubExitState,
      outer,Exp.outer,hrun,hdec,hdec',hfalse,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange]


theorem run_csubCall_last_h4 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3253h
      (csubCall4State z s mem n bsize esize msize 1) =
      some (csubExit4State z s mem n bsize esize msize) := by
  have hdec : UInt256.lnot (UInt256.ofNat 0) + UInt256.ofNat 1 = UInt256.ofNat 0 := by decide
  have hdec' : UInt256.lnot (0 : UInt256) + UInt256.ofNat 1 = UInt256.ofNat 0 := hdec
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hdecMax : Monpro.maxWord + UInt256.ofNat 1 = UInt256.ofNat 0 := by
    rw [show Monpro.maxWord = UInt256.lnot (UInt256.ofNat 0) by decide]
    exact hdec
  simp (config := { maxSteps := 200000 })
    [blk3253h,hdecMax,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csubCall4State,slotKState,rideSlots,entrySlots,shiftEntry,pcCsubCall,pcCsubExit,
      csubExit4State,
      outer,Exp.outer,hrun,hdec,hdec',hfalse,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange]


/-- `blk3253x`: the loop exit jumps to `SHIFT_DONE`. -/
theorem run_csubExit (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3253x
      (csubExitState z s mem n bsize esize msize) =
      some (shiftDoneState z s mem n bsize esize msize) := by
  simp (config := { maxSteps := 200000 })
    [blk3253x,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csubExitState,shiftDoneState,slotKState,rideSlots,entrySlots,shiftEntry,
      pcCsubExit,pcShiftDone,
      outer,Exp.outer,hcode,hrun,jumpDest5366,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- An initialized cache with a non-single-byte exponent enters the ordinary loop. -/
theorem run_e5 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hfast : n = 4 ∨ n = 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hesize : UInt256.ofNat esize ≠ UInt256.ofNat 1)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock CycleSubmission.Global.Fast.blk2764
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState (UInt256.ofNat 2310) (taggedTemplate s (UInt256.ofNat 0)) mem
        n bsize esize msize n) := by
  have hinitial : initialPhase s mem esize = UInt256.ofNat 0 := by
    have he : UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat esize) = UInt256.ofNat 0 := by
      unfold UInt256.eq
      apply if_neg
      intro h
      exact hesize (Challenge.EvmProof.Word.word_ext h.symm)
    unfold initialPhase
    rw [he]
    simp [UInt256.land, UInt256.ofNat, UInt256.size, Fin.ofNat, Fin.land]
  have shortHead4 : UInt256.ofNat 18724 - UInt256.ofNat 2008 * UInt256.ofNat 4 = UInt256.ofNat 10692 := by decide
  have shortShift4_0 : UInt256.shiftRight (UInt256.ofNat 4) (UInt256.ofNat 0) = UInt256.ofNat 4 := by decide
  have shortShift4_1 : UInt256.shiftRight (UInt256.ofNat 4) (UInt256.ofNat 1) = UInt256.ofNat 2 := by decide
  have shortHead8 : UInt256.ofNat 18724 - UInt256.ofNat 2008 * UInt256.ofNat 8 = UInt256.ofNat 2660 := by decide
  have shortShift8_0 : UInt256.shiftRight (UInt256.ofNat 8) (UInt256.ofNat 0) = UInt256.ofNat 8 := by decide
  have shortShift8_1 : UInt256.shiftRight (UInt256.ofNat 8) (UInt256.ofNat 1) = UInt256.ofNat 4 := by decide
  rcases hfast with h | h <;> subst h <;>
    simp (config := { maxSteps := 300000 })
      [shortHead4, shortHead8, shortShift4_0, shortShift4_1, shortShift8_0, shortShift8_1, CycleSubmission.Global.Fast.blk2764, CycleSubmission.Global.Fast.opAt, CycleSubmission.Global.Fast.pushAt, CycleSubmission.Global.Fast.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
       Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
       cacheSetupState, readyCacheSlots, hinitial, slotKState, shiftLoopState,
       entrySlots, taggedTemplate, phaseTag, headPC, headWord, outer, Exp.outer,
       hcode, hrun, CycleSubmission.Global.Fast.jumpDestHead4, CycleSubmission.Global.Fast.jumpDest4839,
       Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
       Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
       Nat.mod_eq_of_lt, List.exchange]


/-- An initialized exponent-three cache enters the half-length first loop. -/
theorem run_e5_e3 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hfast : n = 4 ∨ n = 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hsize1 : UInt256.ofNat esize = UInt256.ofNat 1)
    (hbyte3 : UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat) =
      UInt256.ofNat 3)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock CycleSubmission.Global.Fast.blk2764
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState (UInt256.ofNat 2310) (taggedTemplate s (UInt256.ofNat 1)) mem
        n bsize esize msize (n / 2)) := by
  have hinitial : initialPhase s mem esize = UInt256.ofNat 1 := by
    unfold initialPhase
    rw [hbyte3, hsize1]
    decide
  have shortHead4 : UInt256.ofNat 18724 - UInt256.ofNat 2008 * UInt256.ofNat 4 = UInt256.ofNat 10692 := by decide
  have shortShift4_0 : UInt256.shiftRight (UInt256.ofNat 4) (UInt256.ofNat 0) = UInt256.ofNat 4 := by decide
  have shortShift4_1 : UInt256.shiftRight (UInt256.ofNat 4) (UInt256.ofNat 1) = UInt256.ofNat 2 := by decide
  have shortHead8 : UInt256.ofNat 18724 - UInt256.ofNat 2008 * UInt256.ofNat 8 = UInt256.ofNat 2660 := by decide
  have shortShift8_0 : UInt256.shiftRight (UInt256.ofNat 8) (UInt256.ofNat 0) = UInt256.ofNat 8 := by decide
  have shortShift8_1 : UInt256.shiftRight (UInt256.ofNat 8) (UInt256.ofNat 1) = UInt256.ofNat 4 := by decide
  rcases hfast with h | h <;> subst h <;>
    simp (config := { maxSteps := 300000 })
      [shortHead4, shortHead8, shortShift4_0, shortShift4_1, shortShift8_0, shortShift8_1, CycleSubmission.Global.Fast.blk2764, CycleSubmission.Global.Fast.opAt, CycleSubmission.Global.Fast.pushAt, CycleSubmission.Global.Fast.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
       Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
       cacheSetupState, readyCacheSlots, hinitial, slotKState, shiftLoopState,
       entrySlots, taggedTemplate, phaseTag, headPC, headWord, outer, Exp.outer,
       hcode, hrun, CycleSubmission.Global.Fast.jumpDestHead4, CycleSubmission.Global.Fast.jumpDest4839,
       Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
       Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
       Nat.mod_eq_of_lt, List.exchange]


/-- Other single-byte exponents enter the ordinary loop with a clear phase flag. -/
theorem run_e5_slowexp (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hfast : n = 4 ∨ n = 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hsize1 : UInt256.ofNat esize = UInt256.ofNat 1)
    (hbyteNe : UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat) ≠
      UInt256.ofNat 3)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock CycleSubmission.Global.Fast.blk2764
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState (UInt256.ofNat 2310) (taggedTemplate s (UInt256.ofNat 0)) mem
        n bsize esize msize n) := by
  have hinitial : initialPhase s mem esize = UInt256.ofNat 0 := by
    have hb : UInt256.eq (UInt256.ofNat 3)
        (UInt256.byteAt (UInt256.ofNat 0)
          (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat)) = UInt256.ofNat 0 := by
      unfold UInt256.eq
      apply if_neg
      intro h
      exact hbyteNe (Challenge.EvmProof.Word.word_ext h.symm)
    unfold initialPhase
    rw [hb]
    simp [UInt256.land, UInt256.ofNat, UInt256.size, Fin.ofNat, Fin.land, Nat.zero_and]
  have shortHead4 : UInt256.ofNat 18724 - UInt256.ofNat 2008 * UInt256.ofNat 4 = UInt256.ofNat 10692 := by decide
  have shortShift4_0 : UInt256.shiftRight (UInt256.ofNat 4) (UInt256.ofNat 0) = UInt256.ofNat 4 := by decide
  have shortShift4_1 : UInt256.shiftRight (UInt256.ofNat 4) (UInt256.ofNat 1) = UInt256.ofNat 2 := by decide
  have shortHead8 : UInt256.ofNat 18724 - UInt256.ofNat 2008 * UInt256.ofNat 8 = UInt256.ofNat 2660 := by decide
  have shortShift8_0 : UInt256.shiftRight (UInt256.ofNat 8) (UInt256.ofNat 0) = UInt256.ofNat 8 := by decide
  have shortShift8_1 : UInt256.shiftRight (UInt256.ofNat 8) (UInt256.ofNat 1) = UInt256.ofNat 4 := by decide
  rcases hfast with h | h <;> subst h <;>
    simp (config := { maxSteps := 300000 })
      [shortHead4, shortHead8, shortShift4_0, shortShift4_1, shortShift8_0, shortShift8_1, CycleSubmission.Global.Fast.blk2764, CycleSubmission.Global.Fast.opAt, CycleSubmission.Global.Fast.pushAt, CycleSubmission.Global.Fast.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
       Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
       cacheSetupState, readyCacheSlots, hinitial, slotKState, shiftLoopState,
       entrySlots, taggedTemplate, phaseTag, headPC, headWord, outer, Exp.outer,
       hcode, hrun, CycleSubmission.Global.Fast.jumpDestHead4, CycleSubmission.Global.Fast.jumpDest4839,
       Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
       Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
       Nat.mod_eq_of_lt, List.exchange]



@[simp] private theorem pcFact4392 :
    CycleSubmission.Artifact.artifact.instructionPC 2970 = 3914 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem pc2706 : CycleSubmission.Artifact.artifact.instructionPC 2403 = 3147 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4393 : CycleSubmission.Artifact.artifact.instructionPC 2971 = 3915 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4394 : CycleSubmission.Artifact.artifact.instructionPC 2972 = 3916 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4395 : CycleSubmission.Artifact.artifact.instructionPC 2973 = 3917 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4396 : CycleSubmission.Artifact.artifact.instructionPC 2974 = 3918 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4397 : CycleSubmission.Artifact.artifact.instructionPC 2975 = 3919 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4398 : CycleSubmission.Artifact.artifact.instructionPC 2976 = 3920 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4399 : CycleSubmission.Artifact.artifact.instructionPC 2977 = 3921 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4400 : CycleSubmission.Artifact.artifact.instructionPC 2978 = 3922 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4403 : CycleSubmission.Artifact.artifact.instructionPC 2981 = 3925 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem pc4402 : CycleSubmission.Artifact.artifact.instructionPC 2980 = 3924 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem pc4401 : CycleSubmission.Artifact.artifact.instructionPC 2979 = 3923 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4404 : CycleSubmission.Artifact.artifact.instructionPC 2982 = 3926 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4405 : CycleSubmission.Artifact.artifact.instructionPC 2983 = 3927 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4406 : CycleSubmission.Artifact.artifact.instructionPC 2984 = 3928 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4407 : CycleSubmission.Artifact.artifact.instructionPC 2985 = 3929 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4408 : CycleSubmission.Artifact.artifact.instructionPC 2986 = 3930 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4409 : CycleSubmission.Artifact.artifact.instructionPC 2987 = 3931 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4410 : CycleSubmission.Artifact.artifact.instructionPC 2988 = 3934 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem pc4411 : CycleSubmission.Artifact.artifact.instructionPC 2989 = 3935 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

/-- `blk3346` with the squaring flag clear: drop the counter and jump to the
cleanup tail. -/
theorem run_cleanup (s : State) (mem : ByteArray) (n bsize esize msize d target : Nat)
    (htarget : 2284 + d = target) (hlt : target < 2 ^ 256)
    (hdest : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode target = true)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk5444
      (cleanupState (UInt256.ofNat d) s mem n bsize esize msize) =
      some (frameState s mem target n bsize esize msize) := by
  have hadd : UInt256.ofNat 2284 + UInt256.ofNat d = UInt256.ofNat target := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod,htarget]
  have hmod : target %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = target :=
    Nat.mod_eq_of_lt hlt
  have hmod' : target % 2 ^ 256 = target := Nat.mod_eq_of_lt hlt
  simp (config := { maxSteps := 3000000 })
    [blk5444,opAt,pushAt,wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cleanupState,slotState,frameState,rideSlots,entrySlots,
      shiftEntry,outer,Exp.outer,hcode,hrun,hadd,htarget,hmod,hmod',hdest,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

end CycleSubmission.Global.Fast.Shift
