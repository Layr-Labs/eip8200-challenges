import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftTrace1

noncomputable section
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

namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift

attribute [local simp] CompactConstants.notThirtyOne notThirtyOneOfNat
attribute [local simp] CompactConstants.notZero CompactConstants.notZeroStruct

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open CycleSubmission.Global.ShiftPCs

theorem run_shiftHead_go (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n ≠ 4)
    (hk : k ≠ 0) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013
      (shiftLoopState z s mem n bsize esize msize k) =
      some (shiftBodyState z s mem n bsize esize msize k) := by
  have hkmod : k % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = k := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 200000 })
    [blk3013, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftBodyState, slotKState, rideSlots, entrySlots, shiftEntry,
      headPC, hw,
      outer, Exp.outer, hcode, hrun, hk, hkmod, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, jumpDest5366]

theorem run_shiftHead_go_h4 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hk : k ≠ 0) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013h
      (shiftLoopState z s mem n bsize esize msize k) =
      some (shiftBodyState z s mem n bsize esize msize k) := by
  have hkmod : k % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = k := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 200000 })
    [blk3013h, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftBodyState, slotKState, rideSlots, entrySlots, shiftEntry,
      headPC, hw,
      outer, Exp.outer, hcode, hrun, hk, hkmod, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, jumpDest5366]

/-- `blk3018`: `MCOPY(TN, TS, s32)` (the retained accumulator shifted up one limb) and `t[0] := 0`. -/
theorem run_shiftBody (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n ≠ 4)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hact : 88 ≤ s.activeWords.toNat)
    (hbs : bsize = 32 * n)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hlimb : 2080 + 32 * n = 2336)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3018
      (shiftBodyState z s mem n bsize esize msize k) =
      some (estimateState z s mem n bsize esize msize k) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * n := Exp.mod_word_self (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix2 : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 2080 (32 * n)) 2112
      (32 * n)) = s.activeWords :=
    Exp.activeWords_fix2 s 2080 (32 * n) 2112 (32 * n) (by omega) (by omega) (by omega)
      (by omega) hact
  have hfixTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2784 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have hfixT0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (2080 + 32 * n) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have htl' : MachineState.readWord
      (MachineState.writeBytes mem (MachineState.readPadded mem 2112 (32 * n)) 2080) 2784 =
      UInt256.ofNat (2080 + 32 * n) := by
    rw [show MachineState.writeBytes mem (MachineState.readPadded mem 2112 (32 * n)) 2080 =
      Exp.mcopyMem mem 2080 2112 (32 * n) from rfl]
    rw [Exp.readWord_mcopyMem_disjoint mem 2080 2112 (32 * n) 2784 (Or.inr (by omega))]
    exact htl
  have hmodTL : (2080 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 2080 + 32 * n := Nat.mod_eq_of_lt (by omega)
  have hbsz : (UInt256.ofNat bsize).toNat = 32 * n := by
    rw [hbs, Challenge.EvmProof.Word.word_toNat_ofNat]
    exact hmod
  have hbsw : UInt256.ofNat bsize = UInt256.ofNat (32 * n) := by
    rw [hbs]
  have huv (a : Nat) (ha : a + 32 ≤ 2080) :
      MachineState.readWord (uMem mem n) a = MachineState.readWord mem a :=
    Shift.uMem_readWord_disjoint mem n a (Or.inl ha)
  have hu1312 := huv 1312 (by omega)
  have hu1344 := huv 1344 (by omega)
  have hu1376 := huv 1376 (by omega)
  have hu1408 := huv 1408 (by omega)
  have hu1440 := huv 1440 (by omega)
  have hu1472 := huv 1472 (by omega)
  have hu1504 := huv 1504 (by omega)
  have hu1632 := huv 1632 (by omega)
  have hu1664 := huv 1664 (by omega)
  have hu1568 := huv 1568 (by omega)
  have hu1536 := huv 1536 (by omega)
  have hu32 := huv 32 (by omega)
  have hlit : UInt256.ofNat 2336 = UInt256.ofNat (2080 + 32 * n) := by rw [hlimb]
  simp (config := { maxSteps := 400000 })
    [blk3018, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftBodyState, estimateState, slotKState, rideSlots, entrySlots, shiftEntry,
      headPC, hw,
      Exp.mcopyMem, Exp.storeWord, outer, Exp.outer, hcode, hrun, hmod, hfix2, hfixTL,
      hfixT0, htl', hmodTL, hlit, hbsz, hbsw, hu1312, hu1344, hu1376, hu1408, hu1440,
      hu1472, hu1504, hu1632, hu1664, hu1568, hu1536, hu32, Exp.push0_word,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  all_goals rfl

theorem run_shiftBody_h4 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hact : 88 ≤ s.activeWords.toNat)
    (hbs : bsize = 32 * n)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hlimb : 2080 + 32 * n = 2208)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3018h
      (shiftBodyState z s mem n bsize esize msize k) =
      some (estimateState z s mem n bsize esize msize k) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * n := Exp.mod_word_self (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix2 : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 2080 (32 * n)) 2112
      (32 * n)) = s.activeWords :=
    Exp.activeWords_fix2 s 2080 (32 * n) 2112 (32 * n) (by omega) (by omega) (by omega)
      (by omega) hact
  have hfixTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2784 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have hfixT0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (2080 + 32 * n) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have htl' : MachineState.readWord
      (MachineState.writeBytes mem (MachineState.readPadded mem 2112 (32 * n)) 2080) 2784 =
      UInt256.ofNat (2080 + 32 * n) := by
    rw [show MachineState.writeBytes mem (MachineState.readPadded mem 2112 (32 * n)) 2080 =
      Exp.mcopyMem mem 2080 2112 (32 * n) from rfl]
    rw [Exp.readWord_mcopyMem_disjoint mem 2080 2112 (32 * n) 2784 (Or.inr (by omega))]
    exact htl
  have hmodTL : (2080 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 2080 + 32 * n := Nat.mod_eq_of_lt (by omega)
  have hbsz : (UInt256.ofNat bsize).toNat = 32 * n := by
    rw [hbs, Challenge.EvmProof.Word.word_toNat_ofNat]
    exact hmod
  have hbsw : UInt256.ofNat bsize = UInt256.ofNat (32 * n) := by
    rw [hbs]
  have huv (a : Nat) (ha : a + 32 ≤ 2080) :
      MachineState.readWord (uMem mem n) a = MachineState.readWord mem a :=
    Shift.uMem_readWord_disjoint mem n a (Or.inl ha)
  have hu1312 := huv 1312 (by omega)
  have hu1344 := huv 1344 (by omega)
  have hu1376 := huv 1376 (by omega)
  have hu1408 := huv 1408 (by omega)
  have hu1440 := huv 1440 (by omega)
  have hu1472 := huv 1472 (by omega)
  have hu1504 := huv 1504 (by omega)
  have hu1632 := huv 1632 (by omega)
  have hu1664 := huv 1664 (by omega)
  have hu1568 := huv 1568 (by omega)
  have hu1536 := huv 1536 (by omega)
  have hu32 := huv 32 (by omega)
  have hpc : headPC n = 10726 := by simp [headPC, hw]
  have hlit : UInt256.ofNat 2208 = UInt256.ofNat (2080 + 32 * n) := by rw [hlimb]
  simp (config := { maxSteps := 400000 })
    [blk3018h, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftBodyState, estimateState, slotKState, rideSlots, entrySlots, shiftEntry,
      hpc,
      Exp.mcopyMem, Exp.storeWord, outer, Exp.outer, hcode, hrun, hmod, hfix2, hfixTL,
      hfixT0, htl', hmodTL, hlit, hbsz, hbsw, hu1312, hu1344, hu1376, hu1408, hu1440,
      hu1472, hu1504, hu1632, hu1664, hu1568, hu1536, hu32, Exp.push0_word,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  all_goals rfl

private theorem ofNat_zero_lt_eq_double_isZero (x : UInt256) :
    UInt256.lt (UInt256.ofNat 0) x = UInt256.isZero (UInt256.isZero x) :=
  Monpro.zero_lt_eq_double_isZero x

private theorem addMod_comm (a b m : UInt256) :
    UInt256.addMod a b m = UInt256.addMod b a m := by
  simp only [UInt256.addMod, Nat.add_comm]

private theorem estimate_notZero_maxWord : UInt256.lnot (⟨0⟩ : UInt256) = Monpro.maxWord := by decide

private theorem estimate_notZeroOfNat_maxWord : UInt256.lnot (UInt256.ofNat 0) = Monpro.maxWord := by
  decide

private theorem estimate_directMax_maxWord :
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 = Monpro.maxWord := by decide

private theorem saturation_gt_eq_lt (a b : UInt256) : a.gt b = b.lt a := by
  unfold UInt256.gt UInt256.lt
  split <;> [skip; skip] <;> simp_all

/-- Use the inherited all-ones sentinel to complement a boolean mask. -/
private theorem sentinel_add_lt (a b : UInt256) :
    Monpro.maxWord + UInt256.lt a b =
      UInt256.ofNat 0 - UInt256.isZero (UInt256.lt a b) := by
  unfold UInt256.lt
  split <;> decide

/-- Boundary before the quotient multiplication; keeps the kernel certificate small. -/
private def estimateMid (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) : State :=
  let U := uMem mem n
  let hi := UInt256.shiftRight (MachineState.readWord U 2080) (MachineState.readWord U 1536)
  let lo := UInt256.shiftRight (MachineState.readWord U 2112) (MachineState.readWord U 1536) +
    UInt256.shiftLeft (MachineState.readWord U 2080) (MachineState.readWord U 1600)
  let diff := lo - UInt256.addMod lo
    (UInt256.mulMod hi (MachineState.readWord U 1632) (MachineState.readWord U 1568))
    (MachineState.readWord U 1568)
  { s with pc := UInt256.ofNat (headPC n + 39)
           memory := uMem0 mem n
           stack := MachineState.readWord U 1664 :: diff :: hi :: UInt256.ofNat k ::
             entrySlots z U n bsize esize ++ outer n bsize esize msize }

private theorem run_estimate_left (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n ≠ 4) (hn2 : 2 ≤ n)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blk3026.take 24)
      (estimateState z s mem n bsize esize msize k) = some (estimateMid z s mem n bsize esize msize k) := by
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hC : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1600 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2112 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hH : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hr2080 := uMem0_readWord mem n 2080 (by omega)
  have hr2112 := uMem0_readWord mem n 2112 (by omega)
  have hr1600 := uMem0_readWord mem n 1600 (by omega)
  have hr0 := uMem0_readWord mem n 0 (by omega)
  simp (config := { maxSteps := 600000 })
    [blk3026, estimateMid, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hr2080, hr2112, hr1600, hr0,
      estimateState, macSetupState, slotKState, rideSlots, entrySlots, shiftEntry,
      headPC, hw, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, hA, hC, hD, hH, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, addMod_comm, saturation_gt_eq_lt,
      estimate_notZero_maxWord, estimate_notZeroOfNat_maxWord, estimate_directMax_maxWord, sentinel_add_lt]

private theorem run_estimate_right (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n ≠ 4) (hn2 : 2 ≤ n)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blk3026.drop 24)
      (estimateMid z s mem n bsize esize msize k) = some (macSetupState z s mem n bsize esize msize k) := by
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hC : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1600 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2112 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hH : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hr2080 := uMem0_readWord mem n 2080 (by omega)
  have hr2112 := uMem0_readWord mem n 2112 (by omega)
  have hr1600 := uMem0_readWord mem n 1600 (by omega)
  have hr0 := uMem0_readWord mem n 0 (by omega)
  simp (config := { maxSteps := 600000 })
    [blk3026, estimateMid, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hr2080, hr2112, hr1600, hr0,
      estimateState, macSetupState, slotKState, rideSlots, entrySlots, shiftEntry,
      headPC, hw, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, hA, hC, hD, hH, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, addMod_comm, saturation_gt_eq_lt,
      estimate_notZero_maxWord, estimate_notZeroOfNat_maxWord, estimate_directMax_maxWord, sentinel_add_lt]

theorem run_estimate (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n ≠ 4) (hn2 : 2 ≤ n)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3026
      (estimateState z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
  have h := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (blk3026.take 24) (blk3026.drop 24)
    (estimateState z s mem n bsize esize msize k) (estimateMid z s mem n bsize esize msize k) (macSetupState z s mem n bsize esize msize k)
    (run_estimate_left z s mem n bsize esize msize k hw hn2 hact hcode hrun) hrun
    (run_estimate_right z s mem n bsize esize msize k hw hn2 hact hcode hrun)
  simpa only [List.take_append_drop] using h

private def estimateRawPart0 : List YulEvmCompiler.Instr :=
  [.push 2 2080,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1600,
   .op .MLOAD]

private def estimateRawPart1 : List YulEvmCompiler.Instr :=
  [.op .SHL,
   .push 2 2112,
   .op .MLOAD,
   .op (.Dup ⟨15, by decide⟩),
   .op .SHR,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨0, by decide⟩)]

private def estimateRawPart2 : List YulEvmCompiler.Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADDMOD,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩)]

private def estimateRawPart3 : List YulEvmCompiler.Instr :=
  [.op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .push 1 128,
   .op .SHR,
   .op .MUL,
   .op (.Dup ⟨1, by decide⟩),
   .push 0 0]

private def estimateRawPart4 : List YulEvmCompiler.Instr :=
  [.op .MLOAD,
   .op .MUL,
   .push 2 2112,
   .op .MLOAD,
   .op .SUB,
   .op .LT,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB]

private def estimateRawPart5 : List YulEvmCompiler.Instr :=
  [.push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .GT,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op .OR]

private def estimate8 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) : State :=
  let U := uMem mem n
  let v0 : UInt256 := MachineState.readWord U 2080
  let v1 : UInt256 := UInt256.shiftRight v0 (MachineState.readWord U 1536)
  let v2 : UInt256 := MachineState.readWord U 1600
  { s with pc := UInt256.ofNat (headPC n + 21)
           memory := uMem0 mem n
           stack := v2 :: v0 :: v1 :: UInt256.ofNat k ::
             entrySlots z U n bsize esize ++ outer n bsize esize msize }

private def estimate16 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) : State :=
  let U := uMem mem n
  let v0 : UInt256 := MachineState.readWord U 2080
  let v1 : UInt256 := UInt256.shiftRight v0 (MachineState.readWord U 1536)
  let v2 : UInt256 := MachineState.readWord U 1600
  let v3 : UInt256 := UInt256.shiftLeft v0 v2
  let v4 : UInt256 := MachineState.readWord U 2112
  let v5 : UInt256 := UInt256.shiftRight v4 (MachineState.readWord U 1536)
  let v6 : UInt256 := v5 + v3
  { s with pc := UInt256.ofNat (headPC n + 31)
           memory := uMem0 mem n
           stack := (MachineState.readWord U 1568) :: (MachineState.readWord U 1568) :: v6 :: v1 :: UInt256.ofNat k ::
             entrySlots z U n bsize esize ++ outer n bsize esize msize }

private def estimate32 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) : State :=
  let U := uMem mem n
  let v0 : UInt256 := MachineState.readWord U 2080
  let v1 : UInt256 := UInt256.shiftRight v0 (MachineState.readWord U 1536)
  let v2 : UInt256 := MachineState.readWord U 1600
  let v3 : UInt256 := UInt256.shiftLeft v0 v2
  let v4 : UInt256 := MachineState.readWord U 2112
  let v5 : UInt256 := UInt256.shiftRight v4 (MachineState.readWord U 1536)
  let v6 : UInt256 := v5 + v3
  let v7 : UInt256 := UInt256.mulMod v1 (MachineState.readWord U 1632) (MachineState.readWord U 1568)
  let v8 : UInt256 := UInt256.addMod v6 v7 (MachineState.readWord U 1568)
  let v9 : UInt256 := v6 - v8
  let v10 : UInt256 := (MachineState.readWord U 1664) * v9
  let v11 : UInt256 := UInt256.shiftRight v10 (UInt256.ofNat 128)
  let v12 : UInt256 := v11 * (UInt256.shiftRight (MachineState.readWord U 32) (UInt256.ofNat 128))
  { s with pc := UInt256.ofNat (headPC n + 48)
           memory := uMem0 mem n
           stack := (UInt256.ofNat 0) :: v10 :: v12 :: v10 :: v1 :: UInt256.ofNat k ::
             entrySlots z U n bsize esize ++ outer n bsize esize msize }

private def estimate40 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) : State :=
  let U := uMem mem n
  let v0 : UInt256 := MachineState.readWord U 2080
  let v1 : UInt256 := UInt256.shiftRight v0 (MachineState.readWord U 1536)
  let v2 : UInt256 := MachineState.readWord U 1600
  let v3 : UInt256 := UInt256.shiftLeft v0 v2
  let v4 : UInt256 := MachineState.readWord U 2112
  let v5 : UInt256 := UInt256.shiftRight v4 (MachineState.readWord U 1536)
  let v6 : UInt256 := v5 + v3
  let v7 : UInt256 := UInt256.mulMod v1 (MachineState.readWord U 1632) (MachineState.readWord U 1568)
  let v8 : UInt256 := UInt256.addMod v6 v7 (MachineState.readWord U 1568)
  let v9 : UInt256 := v6 - v8
  let v10 : UInt256 := (MachineState.readWord U 1664) * v9
  let v11 : UInt256 := UInt256.shiftRight v10 (UInt256.ofNat 128)
  let v12 : UInt256 := v11 * (UInt256.shiftRight (MachineState.readWord U 32) (UInt256.ofNat 128))
  let v13 : UInt256 := MachineState.readWord U 0
  let v14 : UInt256 := v13 * v10
  let v15 : UInt256 := MachineState.readWord U 2112
  let v16 : UInt256 := v15 - v14
  let v17 : UInt256 := UInt256.lt v16 v12
  let v18 : UInt256 := v10 - v17
  { s with pc := UInt256.ofNat (headPC n + 58)
           memory := uMem0 mem n
           stack := v18 :: v1 :: UInt256.ofNat k ::
             entrySlots z U n bsize esize ++ outer n bsize esize msize }

private theorem run_estimate_h4_part0 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    WindowNibbleKernel.runInstructions estimateRawPart0
      (estimateState z s mem n bsize esize msize k) = some (estimate8 z s mem n bsize esize msize k) := by
  have hn2 : 2 ≤ n := by omega
  have hhead : headPC n = 10726 := by simp [headPC, hw]
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hC : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1600 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2112 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hH : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hr2080 := uMem0_readWord mem n 2080 (by omega)
  have hr2112 := uMem0_readWord mem n 2112 (by omega)
  have hr1600 := uMem0_readWord mem n 1600 (by omega)
  have hr0 := uMem0_readWord mem n 0 (by omega)
  simp (config := { maxSteps := 600000 })
    [estimateRawPart0, WindowNibbleKernel.runInstructions, estimateMid, estimate8, estimate16, estimate32, estimate40, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hr2080, hr2112, hr1600, hr0,
      estimateState, macSetupState, slotKState, rideSlots, entrySlots, shiftEntry,
      hhead, if_pos hw, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, hA, hC, hD, hH, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, addMod_comm, saturation_gt_eq_lt,
      estimate_notZero_maxWord, estimate_notZeroOfNat_maxWord, estimate_directMax_maxWord, sentinel_add_lt]

private theorem run_estimate_h4_part1 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    WindowNibbleKernel.runInstructions estimateRawPart1
      (estimate8 z s mem n bsize esize msize k) = some (estimate16 z s mem n bsize esize msize k) := by
  have hn2 : 2 ≤ n := by omega
  have hhead : headPC n = 10726 := by simp [headPC, hw]
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hC : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1600 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2112 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hH : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hr2080 := uMem0_readWord mem n 2080 (by omega)
  have hr2112 := uMem0_readWord mem n 2112 (by omega)
  have hr1600 := uMem0_readWord mem n 1600 (by omega)
  have hr0 := uMem0_readWord mem n 0 (by omega)
  simp (config := { maxSteps := 600000 })
    [estimateRawPart1, WindowNibbleKernel.runInstructions, estimateMid, estimate8, estimate16, estimate32, estimate40, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hr2080, hr2112, hr1600, hr0,
      estimateState, macSetupState, slotKState, rideSlots, entrySlots, shiftEntry,
      hhead, if_pos hw, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, hA, hC, hD, hH, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, addMod_comm, saturation_gt_eq_lt,
      estimate_notZero_maxWord, estimate_notZeroOfNat_maxWord, estimate_directMax_maxWord, sentinel_add_lt]

private theorem run_estimate_h4_part2 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    WindowNibbleKernel.runInstructions estimateRawPart2
      (estimate16 z s mem n bsize esize msize k) = some (estimateMid z s mem n bsize esize msize k) := by
  have hn2 : 2 ≤ n := by omega
  have hhead : headPC n = 10726 := by simp [headPC, hw]
  simp (config := { maxSteps := 600000 })
    [estimateRawPart2, WindowNibbleKernel.runInstructions, estimateMid, estimate8, estimate16, estimate32, estimate40, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      estimateState, macSetupState, slotKState, rideSlots, entrySlots, shiftEntry,
      hhead, if_pos hw, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, addMod_comm, saturation_gt_eq_lt,
      estimate_notZero_maxWord, estimate_notZeroOfNat_maxWord, estimate_directMax_maxWord, sentinel_add_lt]

private theorem run_estimate_h4_part3 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    WindowNibbleKernel.runInstructions estimateRawPart3
      (estimateMid z s mem n bsize esize msize k) = some (estimate32 z s mem n bsize esize msize k) := by
  have hn2 : 2 ≤ n := by omega
  have hhead : headPC n = 10726 := by simp [headPC, hw]
  simp (config := { maxSteps := 600000 })
    [estimateRawPart3, WindowNibbleKernel.runInstructions, estimateMid, estimate8, estimate16, estimate32, estimate40, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      estimateState, macSetupState, slotKState, rideSlots, entrySlots, shiftEntry,
      hhead, if_pos hw, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, addMod_comm, saturation_gt_eq_lt,
      estimate_notZero_maxWord, estimate_notZeroOfNat_maxWord, estimate_directMax_maxWord, sentinel_add_lt]

private theorem run_estimate_h4_part4 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    WindowNibbleKernel.runInstructions estimateRawPart4
      (estimate32 z s mem n bsize esize msize k) = some (estimate40 z s mem n bsize esize msize k) := by
  have hn2 : 2 ≤ n := by omega
  have hhead : headPC n = 10726 := by simp [headPC, hw]
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hC : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1600 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2112 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hH : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hr2080 := uMem0_readWord mem n 2080 (by omega)
  have hr2112 := uMem0_readWord mem n 2112 (by omega)
  have hr1600 := uMem0_readWord mem n 1600 (by omega)
  have hr0 := uMem0_readWord mem n 0 (by omega)
  simp (config := { maxSteps := 600000 })
    [estimateRawPart4, WindowNibbleKernel.runInstructions, estimateMid, estimate8, estimate16, estimate32, estimate40, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hr2080, hr2112, hr1600, hr0,
      estimateState, macSetupState, slotKState, rideSlots, entrySlots, shiftEntry,
      hhead, if_pos hw, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, hA, hC, hD, hH, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, addMod_comm, saturation_gt_eq_lt,
      estimate_notZero_maxWord, estimate_notZeroOfNat_maxWord, estimate_directMax_maxWord, sentinel_add_lt]

private theorem run_estimate_h4_part5 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    WindowNibbleKernel.runInstructions estimateRawPart5
      (estimate40 z s mem n bsize esize msize k) = some (macSetupState z s mem n bsize esize msize k) := by
  have hn2 : 2 ≤ n := by omega
  have hhead : headPC n = 10726 := by simp [headPC, hw]
  simp (config := { maxSteps := 600000 })
    [estimateRawPart5, WindowNibbleKernel.runInstructions, estimateMid, estimate8, estimate16, estimate32, estimate40, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      estimateState, macSetupState, slotKState, rideSlots, entrySlots, shiftEntry,
      hhead, if_pos hw, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, addMod_comm, saturation_gt_eq_lt,
      estimate_notZero_maxWord, estimate_notZeroOfNat_maxWord, estimate_directMax_maxWord, sentinel_add_lt]

private theorem estimate_h4_program :
    blk3026h.map Challenge.EvmProof.Stepper.Located.instruction =
      estimateRawPart0 ++ (estimateRawPart1 ++ (estimateRawPart2 ++ (estimateRawPart3 ++ (estimateRawPart4 ++ (estimateRawPart5))))) := by rfl

private theorem estimate_h4_layout :
    WindowTwentyOneLocated.LinearPath (UInt256.ofNat 10735) blk3026h := by
  dsimp only [blk3026h, opAt, pushAt, wfOp,
    WindowTwentyOneLocated.LinearPath, WindowTwentyOneLocated.Linear]
  simp [YulEvmCompiler.Instr.size_push, YulEvmCompiler.Instr.size_op,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_estimate_h4 (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hw : n = 4)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3026h
      (estimateState z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
  have hraw := (WindowNibbleKernel.runInstructions_append_some _ _ _ _ _
      (run_estimate_h4_part0 z s mem n bsize esize msize k hw hact hcode hrun) (WindowNibbleKernel.runInstructions_append_some _ _ _ _ _
      (run_estimate_h4_part1 z s mem n bsize esize msize k hw hact hcode hrun) (WindowNibbleKernel.runInstructions_append_some _ _ _ _ _
      (run_estimate_h4_part2 z s mem n bsize esize msize k hw hact hcode hrun) (WindowNibbleKernel.runInstructions_append_some _ _ _ _ _
      (run_estimate_h4_part3 z s mem n bsize esize msize k hw hact hcode hrun) (WindowNibbleKernel.runInstructions_append_some _ _ _ _ _
      (run_estimate_h4_part4 z s mem n bsize esize msize k hw hact hcode hrun) (run_estimate_h4_part5 z s mem n bsize esize msize k hw hact hcode hrun))))))
  refine WindowTwentyOneLocated.run_linear blk3026h (UInt256.ofNat 10735)
    (estimateState z s mem n bsize esize msize k) (macSetupState z s mem n bsize esize msize k)
    ?_ estimate_h4_layout ?_ hrun ?_
  · change CycleSubmission.Artifact.bytecode.size < 2 ^ 256
    rw [CycleSubmission.Artifact.bytecodeSize]
    decide
  · simp [estimateState, slotKState, headPC, hw]
  · rw [estimate_h4_program]
    exact hraw

/-- Both loop heads are jump destinations. -/
theorem jumpDestHead (n : Nat) :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode (headPC n) = true := by
  unfold headPC
  split_ifs
  · exact jumpDestHead4
  · exact jumpDest4839

end CycleSubmission.Global.Fast.Shift
