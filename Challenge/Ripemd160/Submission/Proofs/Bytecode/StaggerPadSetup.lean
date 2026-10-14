import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadZeroPrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPadStore
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Setup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadShiftDiet
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPad
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory
open PairTableActive StaggerTableSparse StaggerTableLayout

/-- Pad-only low block (pc 65..102): copy zero calldata over the table (the copy offset is the
last message block's offset in slot 11, which is past the calldata), store the unmasked low
bit-length word `n <<< 3` three times, `0x80` at 522, and the two `0x80` bytes at 67 and 85.  Only the
fast entry (lengths 64, 128, 192) reaches this block, so the high length words are always zero. -/
def lowTemplate : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 1084),
    .op (.Dup ⟨12, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 28),
    .op .CALLDATACOPY,
    .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 3),
    .op .SHL,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 666),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨0, by decide⟩),
    .op .PC,
    .op .MSTORE8,
    .push ⟨2, by decide⟩ (UInt256.ofNat 67),
    .op .MSTORE8,
    .push ⟨2, by decide⟩ (UInt256.ofNat 522),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 162),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .MSTORE ]

/-- `PUSH2 0x128c SWAP13 POP PUSH2 0338 JUMP` at 102: the output entry 4748 becomes the
continuation in slot 12 and the block goes straight to the rounds. -/
def branchTemplate : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 4748),
    .op (.Swap ⟨12, by decide⟩),
    .op .POP,
    .push ⟨2, by decide⟩ (UInt256.ofNat 824),
    .op .JUMP ]

private theorem byte128 (i : Nat) (hi : i < 32) :
    (Data.Bytes.natToBytesPadded (UInt256.ofNat 128).toNat 32)[i]?.getD 0 =
      if i = 31 then 128 else 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
  have h : ∀ j : Fin 32,
      UInt8.ofNat ((UInt256.ofNat 128).toNat / 256 ^ (32 - 1 - j.val) % 256) =
        if j.val = 31 then 128 else 0 := by decide
  exact h ⟨i, hi⟩

/-- On memory that is zero from 36 to 85, the two `0x80` bytes at 85 and 67 are the two word
stores of 128 at 54 and 36 of the table model. -/
theorem pack_two_bytes (memory : ByteArray) (hsize : 86 ≤ memory.size)
    (hzero : ∀ i, 36 ≤ i → i < 86 → memory[i]?.getD 0 = 0) :
    writeWord (writeWord memory 54 (UInt256.ofNat 128)) 36 (UInt256.ofNat 128) =
      MachineState.writeBytes (MachineState.writeBytes memory (ByteArray.mk #[UInt8.ofNat (128 % 256)]) 85)
        (ByteArray.mk #[UInt8.ofNat (128 % 256)]) 67 := by
  have e1 : (ByteArray.mk #[UInt8.ofNat (128 % 256)]).size = 1 := rfl
  apply ByteArray.ext_getElem
  · simp only [writeWord_size, MachineState.writeBytes_size, e1]
    split_ifs <;> omega
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, e1]
    by_cases h36 : 36 ≤ i ∧ i < 36 + 32
    · rw [if_pos h36, byte128 _ (by omega)]
      by_cases h67 : i = 67
      · subst h67; simp; rfl
      · rw [if_neg (by omega)]
        by_cases h85 : 85 ≤ i ∧ i < 85 + 1
        · omega
        · rw [if_neg h85, if_neg (by omega)]
          exact (hzero i h36.1 (by omega)).symm
    · by_cases h54 : 54 ≤ i ∧ i < 54 + 32
      · rw [if_neg h36, if_pos h54, byte128 _ (by omega)]
        by_cases h85 : i = 85
        · subst h85; simp; rfl
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          exact (hzero i (by omega) (by omega)).symm
      · rw [if_neg h36, if_neg h54, if_neg (by omega), if_neg (by omega)]

/-- Pad-only high block (pc 4833..4860), reached only when `n >>> 29 ≠ 0`. -/
def highTemplate : List Instr :=
  [ .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 29),
    .op .SHR,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1008),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 990),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 648),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 612),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 270),
    .op .MSTORE ]

private theorem add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a + b) :=
  Word.ofNat_add_mod a b

private theorem hadd_literals (a b : Nat) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  add_literals a b

private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

/-- The fast padding path is valid for lengths below the artifact's byte size. -/
def highZero (n : UInt256) : UInt256 := UInt256.lt n (UInt256.ofNat 5247)

theorem highZero_true_iff (n : UInt256) :
    UInt256.isTrue (highZero n) ↔ n.toNat < 5247 := by
  change (UInt256.lt n (UInt256.ofNat 5247)).toNat ≠ 0 ↔ n.toNat < 5247
  rw [Word.word_toNat_lt]
  have hc : (UInt256.ofNat 5247).toNat = 5247 := by decide
  rw [hc]
  by_cases hn : n.toNat < 5247 <;> simp [hn]

theorem highZero_true_imp (n : UInt256) (h : UInt256.isTrue (highZero n)) :
    StaggerTablePad.highDirty n = UInt256.ofNat 0 := by
  have hbound := (highZero_true_iff n).mp h
  apply Word.word_ext
  unfold StaggerTablePad.highDirty
  rw [Word.shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow]
  have h0 : (UInt256.ofNat 0).toNat = 0 := by decide
  rw [h0]
  simp only [Nat.reducePow]
  omega

theorem run_low (s : State) (pc : UInt256) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 off : UInt256)
    (rest : List UInt256)
    (hstack : rest.length ≤ 980) (hrun : s.halt = .Running) (hactive : 35 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hoff : s.executionEnv.calldata.size ≤ off.toNat)
    (hpc : pc = UInt256.ofNat 65) :
    runInstrSeq lowTemplate
        {s with pc := pc, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: off :: rest} =
      some {s with
             pc := pcAfter pc lowTemplate
             stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: off :: rest
             memory := StaggerTablePad.padRealChain s.memory
               (UInt256.ofNat s.executionEnv.calldata.size)} := by
  subst hpc
  have hcap (n : Nat) (hn : n ≤ 28) : rest.length + 12 + n < 1024 := by omega
  have hcap' (n : Nat) (hn : n ≤ 28) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved _ _ hactive ha
  have hbyteActive (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 1) = s.activeWords := by
    have he : MachineState.activeWordsAfter s.activeWords.toNat address 1 = s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : (1 : Nat) ≠ 0)]
      apply Nat.max_eq_left
      omega
    rw [he]
    exact (Word.word_eq_ofNat_toNat _).symm
  have hcopyActive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 28 1084) = s.activeWords := by
    have he : MachineState.activeWordsAfter s.activeWords.toNat 28 1084 = s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : (1084 : Nat) ≠ 0)]
      apply Nat.max_eq_left
      omega
    rw [he]
    exact (Word.word_eq_ofNat_toNat _).symm
  have hsize : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  have hzero : MachineState.readPadded s.executionEnv.calldata off.toNat 1084 = PadZeroPrefix.zeroBytes :=
    PadZeroPrefix.readPadded_ge _ _ hoff
  let low := StaggerTablePad.lowDirty (UInt256.ofNat s.executionEnv.calldata.size)
  let base := MachineState.writeBytes s.memory PadZeroPrefix.zeroBytes 28
  let b666 := writeWord base 666 low
  let b8567 := MachineState.writeBytes (MachineState.writeBytes b666 (ByteArray.mk #[UInt8.ofNat (128 % 256)]) 85)
    (ByteArray.mk #[UInt8.ofNat (128 % 256)]) 67
  have hbase_size : 1112 ≤ base.size := by
    change 1112 ≤ (MachineState.writeBytes s.memory PadZeroPrefix.zeroBytes 28).size
    rw [MachineState.writeBytes_size, PadZeroPrefix.zeroBytes_size, if_neg (by decide)]
    exact Nat.le_max_right _ _
  have hb666_size : 86 ≤ b666.size := by
    change 86 ≤ (writeWord base 666 low).size
    rw [writeWord_size]
    exact le_trans (le_trans (by decide) hbase_size) (Nat.le_max_left _ _)
  have hb666_zero : ∀ i, 36 ≤ i → i < 86 → b666[i]?.getD 0 = 0 := by
    intro i hlo hhi
    simp only [b666, base, writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, PadZeroPrefix.zeroBytes_size]
    rw [if_neg (by omega), if_pos (by omega), PadZeroPrefix.zeroBytes_getD]
  have hpacked : StaggerTablePad.padRealChain s.memory (UInt256.ofNat s.executionEnv.calldata.size) =
      writeWord (writeWord (writeWord b8567 522 (UInt256.ofNat 128)) 162 low) 144 low := by
    change StaggerTablePad.lowChainOver base (UInt256.ofNat s.executionEnv.calldata.size) =
      writeWord (writeWord (writeWord b8567 522 (UInt256.ofNat 128)) 162 low) 144 low
    unfold StaggerTablePad.lowChainOver
    change writeWord (writeWord (writeWord (writeWord (writeWord (writeWord base 162 low) 666 low) 144 low) 522 (UInt256.ofNat 128)) 54 (UInt256.ofNat 128)) 36 (UInt256.ofNat 128) =
      writeWord (writeWord (writeWord b8567 522 (UInt256.ofNat 128)) 162 low) 144 low
    have hc : writeWord (writeWord base 162 low) 666 low = writeWord b666 162 low :=
      StaggerTablePad.padWriteWord_comm base 162 666 low low (Or.inl (by decide))
    dsimp only [b8567]
    rw [hc, ← pack_two_bytes b666 hb666_size hb666_zero]
    rw [StaggerTablePad.padWriteWord_comm _ 36 522 _ _ (Or.inl (by decide)),
        StaggerTablePad.padWriteWord_comm _ 54 522 _ _ (Or.inl (by decide)),
        StaggerTablePad.padWriteWord_comm _ 36 162 _ _ (Or.inl (by decide)),
        StaggerTablePad.padWriteWord_comm _ 54 162 _ _ (Or.inl (by decide)),
        StaggerTablePad.padWriteWord_comm _ 522 162 _ _ (Or.inr (by decide)),
        StaggerTablePad.padWriteWord_comm _ 36 144 _ _ (Or.inl (by decide)),
        StaggerTablePad.padWriteWord_comm _ 54 144 _ _ (Or.inl (by decide)),
        StaggerTablePad.padWriteWord_comm _ 522 144 _ _ (Or.inr (by decide))]
  rw [hpacked]
  simp (discharger := omega) [b8567, b666, base, low, lowTemplate, StaggerTablePad.lowDirty,
    writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    PairedHelperBooleanTrace.push0_toNat,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap, hcap',
    State.activeWordsAfterUInt256, hactiveAt, hbyteActive, hcopyActive, hsize, hzero,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]

theorem run_high (s : State) (pc returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) (hactive : 35 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256) :
    runInstrSeq highTemplate {s with pc := pc, stack := returnPC :: rest} =
      some {s with
             pc := pcAfter pc highTemplate
             stack := returnPC :: rest
             memory := StaggerTablePad.highStores s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved _ _ hactive ha
  have hsize : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  simp (discharger := omega) [highTemplate, StaggerTablePad.highStores, StaggerTablePad.highDirty,
    writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, hsize, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [add_eq_hAdd]

theorem run_branch_taken (s : State) (pc : UInt256)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 off c : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 824).toNat = true) :
    runInstrSeq branchTemplate
        {s with pc := pc, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: off :: c :: rho} =
      some {s with
        pc := UInt256.ofNat 824
        stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: off :: UInt256.ofNat 4748 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 16) : rho.length + n < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [branchTemplate, runInstrSeq, DataStepper.runInstr, hrun, hcap,
    hvalid, List.length_cons, List.exchange, List.getElem?_cons_zero, pcAfter, UInt256.succ,
    Instr.size, Nat.add_assoc, Word.word_toNat_ofNat, Word.literal_eq_ofNat]

#print axioms run_low
#print axioms run_high
#print axioms run_branch_taken
#print axioms highZero_true_iff
#print axioms highZero_true_imp
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPad
