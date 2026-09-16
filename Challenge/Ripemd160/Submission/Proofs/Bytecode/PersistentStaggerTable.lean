import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreGap
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableActive
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableCongruence
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlyContract
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScratch
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTable
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairStoreGap

def messagePointer (i : Nat) : Nat := Padding.messageOffset + DriverTrace.blockOffset i

/-- Block model context.  The message block is required in memory only for data blocks: the
pad-only block (the one starting exactly at the end of the input, which exists only when the
input length is a multiple of 64) is scheduled from the calldata size alone. -/
structure Context (s : State) (input : ByteArray) (next : Nat) : Prop where
  calldata : s.executionEnv.calldata = input
  active : 35 ≤ s.activeWords.toNat
  allocated : ∀ i, i < DriverTrace.blockCount input → input.size ≠ DriverTrace.blockOffset i →
    (messagePointer i + 95) / 32 ≤ s.activeWords.toNat
  messageBlock : ∀ i, next ≤ i → i < DriverTrace.blockCount input → input.size ≠ DriverTrace.blockOffset i →
    ScheduleCorrect.MessageBlockAt s.memory (DriverTrace.messageOffsetWord i)
      (Padding.paddedMessage input) (DriverTrace.blockOffset i)
  separated : ∀ i, i < DriverTrace.blockCount input → ∀ k, k < 16 →
    1056 + i * 64 ≤ (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord i) k).toNat
  /-- The first memory word is a clean 32-bit word BELOW BIT 144, so the unmasked loads of
  schedule words 1 and 2 see zero bytes at 14..27.  Bytes 10..13 may carry the dual lane the
  writer's slot-0 store leaves behind once the mask at pc 873 is gone; that lane lives at
  bits 144..175 and is erased again by the store eighteen bytes below every slot that
  carries it. -/
  lowClear : (MachineState.readWord s.memory 0).toNat % 2 ^ 144 < 2 ^ 32
  /-- Four skipped-store gap bytes for each of the thirteen equal table pairs. -/
  gapClear : GapClear s.memory

def blockWords (input : ByteArray) (i : Nat) : Nat → UInt32 :=
  fun k => (CompressionCorrect.schedule (Padding.paddedMessage input)
    (DriverTrace.blockOffset i))[k]!

theorem blockWords_eq_readLE32 (input : ByteArray) (i k : Nat) (hk : k < 16) :
    blockWords input i k = Crypto.Ripemd160.readLE32 (Padding.paddedMessage input)
      (DriverTrace.blockOffset i + k * 4) := by
  interval_cases k <;> simp [blockWords, CompressionCorrect.schedule, List.range']

theorem messagePointer_lower (i : Nat) : 1056 ≤ messagePointer i := by
  simp only [messagePointer, Padding.messageOffset]
  omega

theorem messagePointer_bound (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    messagePointer i + 64 < 2^256 := by
  have hp := Padding.paddedLength_lt input.size
  have heq := DriverTrace.paddedLength_eq_blockCount input
  have hoff : DriverTrace.blockOffset i < Padding.paddedLength input.size := by
    unfold DriverTrace.blockOffset
    omega
  unfold CalldataFits at hfit
  norm_num [messagePointer, Padding.messageOffset] at hfit ⊢
  omega

def selectedWords (s : State) (i : Nat) : Nat → UInt256 :=
  StaggerScratch.dirtyWord s.memory (messagePointer i)

/-- One block's schedule step.  Data blocks load their words from memory; the pad-only block
builds its table from the calldata size and touches no memory above the table. -/
def scheduledState (s : State) (i : Nat) : State :=
  if s.executionEnv.calldata.size = DriverTrace.blockOffset i then
    {s with memory := StaggerTablePad.padRealResult s.memory (UInt256.ofNat s.executionEnv.calldata.size)}
  else
    {s with memory := StaggerTableLayout.resultMemory0 s.memory (selectedWords s i), activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))}

theorem scheduledState_hit (s : State) (i : Nat)
    (hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i) :
    scheduledState s i =
      {s with memory := StaggerTablePad.padRealResult s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  unfold scheduledState; rw [if_pos hh]

theorem scheduledState_miss (s : State) (i : Nat)
    (hh : ¬ s.executionEnv.calldata.size = DriverTrace.blockOffset i) :
    scheduledState s i =
      {s with memory := StaggerTableLayout.resultMemory0 s.memory (selectedWords s i), activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))} := by
  unfold scheduledState; rw [if_neg hh]

theorem scheduled_active (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input i) :
    35 ≤ (scheduledState s i).activeWords.toNat := by
  by_cases hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i
  · rw [scheduledState_hit s i hh]; exact ctx.active
  · rw [scheduledState_miss s i hh]
    exact Stagger144Active.loaded_active_ge35 s (messagePointer i)
      (messagePointer_lower i) (messagePointer_bound input hfit i hi)

theorem extracted_words (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input i) (hne : input.size ≠ DriverTrace.blockOffset i) (k : Nat) (hk : k < 16) :
    PairedScheduleData.extractedWord s.memory (messagePointer i) k = Word.ofUInt32 (blockWords input i k) := by
  rw [PairedScheduleData.extractedWord_eq_expectedWord _ _ _ hk
    (messagePointer_bound input hfit i hi)]
  change ScheduleCorrect.expectedWord s.memory (DriverTrace.messageOffsetWord i) k = _
  rw [ctx.messageBlock i (Nat.le_refl i) hi hne k hk, blockWords_eq_readLE32 input i k hk]

theorem size_word_lt (input : ByteArray) (hfit : CalldataFits input) :
    (UInt256.ofNat input.size).toNat < 2 ^ 64 := by
  unfold CalldataFits at hfit
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hfit

theorem size_word_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (UInt256.ofNat input.size).toNat = input.size := by
  unfold CalldataFits at hfit
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem pad_words (input : ByteArray) (i : Nat) (hfit : CalldataFits input)
    (hh : input.size = DriverTrace.blockOffset i) (k : Nat) (hk : k < 16) :
    PadOnlySchedule.padWords (UInt256.ofNat input.size) k = Word.ofUInt32 (blockWords input i k) := by
  have hn : input.size % 64 = 0 := by rw [hh, DriverTrace.blockOffset]; omega
  rw [blockWords_eq_readLE32 input i k hk, ← hh]
  exact (PadOnlySchedule.padWords_eq_cryptoWords input hfit hn k hk).symm

/-- The pad-only word 14 is the exact bit-length word plus `input.size / 2 ^ 29` dead lanes. -/
theorem pad_word_fourteen (input : ByteArray) (i : Nat) (hfit : CalldataFits input)
    (hh : input.size = DriverTrace.blockOffset i) :
    (StaggerTablePad.padWordsDirty (UInt256.ofNat input.size) 14).toNat =
      (blockWords input i 14).toNat + input.size / 2 ^ 29 * 2 ^ 32 := by
  rw [StaggerTablePad.padWordsDirty_fourteen, StaggerTablePad.lowDirty_toNat _ (size_word_lt input hfit),
    StaggerTablePad.lowLength_eq_padWords, pad_words input i hfit hh 14 (by decide),
    Word.ofUInt32_toNat, size_word_toNat input hfit]

/-- The pad-only word 15 is the exact bit-length word plus `input.size / 2 ^ 61` dead lanes. -/
theorem pad_word_fifteen (input : ByteArray) (i : Nat) (hfit : CalldataFits input)
    (hh : input.size = DriverTrace.blockOffset i) :
    (StaggerTablePad.padWordsDirty (UInt256.ofNat input.size) 15).toNat =
      (blockWords input i 15).toNat + input.size / 2 ^ 61 * 2 ^ 32 := by
  rw [StaggerTablePad.padWordsDirty_fifteen, StaggerTablePad.highDirty_toNat,
    StaggerTablePad.highLength_eq_padWords, pad_words input i hfit hh 15 (by decide),
    Word.ofUInt32_toNat, size_word_toNat input hfit]

/-- Dead lanes of the pad-only table: word 14 carries fewer than `2 ^ 35`, word 15 fewer than
eight, the others none. -/
def padJunk (input : ByteArray) (k : Nat) : Nat :=
  if k = 14 then input.size / 2 ^ 29 else if k = 15 then input.size / 2 ^ 61 else 0

theorem padJunk_lt (input : ByteArray) (hfit : CalldataFits input) (k : Nat) :
    padJunk input k < 2 ^ 35 := by
  unfold padJunk CalldataFits at *
  split
  · simp only [Nat.reducePow] at *
    omega
  · split
    · simp only [Nat.reducePow] at *
      omega
    · decide

theorem padJunk_small (input : ByteArray) (hfit : CalldataFits input) (k : Nat) (h14 : k ≠ 14) :
    padJunk input k < 8 := by
  unfold padJunk CalldataFits at *
  rw [if_neg h14]
  split
  · simp only [Nat.reducePow] at *
    omega
  · omega

theorem ready (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input i) :
    StaggerMessage.Ready (scheduledState s i).memory (blockWords input i) := by
  by_cases hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i
  · rw [scheduledState_hit s i hh]
    change StaggerMessage.Ready (StaggerTablePad.padRealResult s.memory
      (UInt256.ofNat s.executionEnv.calldata.size)) (blockWords input i)
    -- The real table differs from the model only below byte 14, and `Ready` reads the table
    -- only from byte 14 up plus the low 32 bits at address 0.
    have hagree := StaggerTablePad.padRealResult_agree s.memory
      (UInt256.ofNat s.executionEnv.calldata.size) ctx.lowClear
    refine StaggerMessage.ready_congr_high _ _ _ hagree.2
      (StaggerTablePad.read_zero_low32_of_agree hagree) ?_
    rw [ctx.calldata] at hh ⊢
    rw [StaggerTablePad.resultMemory_eq_table _ _ (size_word_lt input hfit)]
    have hj (k : Nat) := padJunk_lt input hfit k
    have hj8 (k : Nat) (h14 : k ≠ 14) := padJunk_small input hfit k h14
    exact StaggerMessage.ready_junk s.memory _ (blockWords input i) (padJunk input)
      (fun k hk => by
        by_cases h14 : k = 14
        · subst h14
          rw [pad_word_fourteen input i hfit hh]
          rfl
        by_cases h15 : k = 15
        · subst h15
          rw [pad_word_fifteen input i hfit hh]
          rfl
        · rw [StaggerTablePad.padWordsDirty_ne _ _ h14 h15, pad_words input i hfit hh k hk,
            Word.ofUInt32_toNat]
          simp only [padJunk, if_neg h14, if_neg h15, Nat.zero_mul, Nat.add_zero])
      (fun k _ => Nat.lt_trans (hj k) (by decide))
      (fun k _ _ => hj k)
      (fun k _ _ h14 => Nat.lt_trans (hj8 k h14) (by decide))
      (fun k _ hd => by
        have h14 : k ≠ 14 := fun h => hd (Or.inr (Or.inr h))
        exact ⟨Nat.lt_trans (hj8 k h14) (by decide),
          fun h15 => by simp only [padJunk, if_neg h14, if_neg h15]⟩)
  · rw [scheduledState_miss s i hh]
    rw [ctx.calldata] at hh
    have hsplit (k : Nat) := StaggerScratch.dirtyWord_split s.memory (messagePointer i) k
    refine StaggerMessage.ready_dual0 s.memory (selectedWords s i) (blockWords input i)
      (Nat.lt_of_div_eq_zero (by norm_num) ((hsplit 6).2.2.2 (by decide))) ?_
    exact StaggerMessage.ready_junk s.memory (selectedWords s i) (blockWords input i)
      (fun k => (selectedWords s i k).toNat / 2 ^ 32)
      (fun k hk => by
        show (StaggerScratch.dirtyWord s.memory (messagePointer i) k).toNat = _
        conv_lhs => rw [(hsplit k).1]
        rw [extracted_words s input i hfit hi ctx hh k hk, Word.ofUInt32_toNat]
        rfl)
      (fun k _ => (hsplit k).2.1)
      (fun k _ h2 => Nat.lt_trans ((hsplit k).2.2.1 h2) (by decide))
      (fun k _ h2 _ => (hsplit k).2.2.1 h2)
      (fun k _ hd => by
        have hd' : ¬ (k = 1 ∨ k = 2) := fun h =>
          hd (h.elim (fun h1 => Or.inl h1) (fun h2 => Or.inr (Or.inl h2)))
        have h0 : (selectedWords s i k).toNat / 2 ^ 32 = 0 := (hsplit k).2.2.2 hd'
        exact ⟨by show (selectedWords s i k).toNat / 2 ^ 32 < 2 ^ 23; rw [h0]; decide, fun _ => h0⟩)

theorem scheduled_word_above (s : State) (i address : Nat) (ha : 1120 ≤ address) :
    MachineState.readWord (scheduledState s i).memory address = MachineState.readWord s.memory address := by
  by_cases hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i
  · rw [scheduledState_hit s i hh]
    change MachineState.readWord (StaggerTablePad.padRealResult s.memory _) address = _
    exact StaggerTablePad.read_padRealResult_outside _ _ _ (by omega)
  · rw [scheduledState_miss s i hh]
    exact StaggerTableLayout.read_resultMemory0_outside _ _ _ (by omega)

theorem scheduled_env (s : State) (i : Nat) :
    (scheduledState s i).executionEnv = s.executionEnv := by
  unfold scheduledState; split <;> rfl

theorem scheduled_halt (s : State) (i : Nat) : (scheduledState s i).halt = s.halt := by
  unfold scheduledState; split <;> rfl

theorem scheduled_callStack (s : State) (i : Nat) :
    (scheduledState s i).callStack = s.callStack := by
  unfold scheduledState; split <;> rfl

theorem scheduled_active_mono (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) :
    s.activeWords.toNat ≤ (scheduledState s i).activeWords.toNat := by
  by_cases hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i
  · rw [scheduledState_hit s i hh]
  · rw [scheduledState_miss s i hh]
    exact PairTableActive.loaded_active_mono s (messagePointer i) (messagePointer_bound input hfit i hi)

theorem dirtyWords_bound (memory : ByteArray) (p i : Nat) :
    (StaggerScratch.dirtyWord memory p i).toNat < 2 ^ 112 := by
  have hs := StaggerScratch.dirtyWord_split memory p i
  have he := PairedScheduleData.extractedWord_bound memory p i
  rw [hs.1]
  have hj := hs.2.1
  omega

/-- Preservation belongs to the existing scheduled-state model, so one generic
lemma supplies all thirteen gap ranges after both ordinary and pad-only blocks. -/
theorem scheduled_gapClear (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (ctx : Context s input i) :
    GapClear (scheduledState s i).memory := by
  by_cases hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i
  · rw [scheduledState_hit s i hh]
    change GapClear (StaggerTablePad.padRealResult s.memory
      (UInt256.ofNat s.executionEnv.calldata.size))
    have hmodel : GapClear (StaggerTablePad.resultMemory s.memory
        (UInt256.ofNat s.executionEnv.calldata.size)) := by
      rw [ctx.calldata, StaggerTablePad.resultMemory_eq_table _ _ (size_word_lt input hfit)]
      exact resultMemory_gapClear s.memory _
        (fun k _ => StaggerTablePad.padWordsDirty_bound _ (size_word_lt input hfit) k)
    -- every gap byte is `18 * j + k` with `8 ≤ j` and `14 ≤ k`, i.e. at least 158
    have hagree := StaggerTablePad.padRealResult_agree s.memory
      (UInt256.ofNat s.executionEnv.calldata.size) ctx.lowClear
    intro j hj k hk hk'
    rw [hagree.2 (18 * j + k) (by have := lowerPairSlots_bounds j hj; omega)]
    exact hmodel j hj k hk hk'
  · rw [scheduledState_miss s i hh]
    exact resultMemory0_gapClear s.memory _
      (fun k _ => dirtyWords_bound s.memory (messagePointer i) k)

theorem Context.scheduled (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input i) : Context (scheduledState s i) input (i + 1) := by
  have hm := scheduled_active_mono s input i hfit hi
  refine ⟨?_, ctx.active.trans hm, ?_, ?_, ctx.separated, ?_, scheduled_gapClear s input i hfit ctx⟩
  · rw [scheduled_env]; exact ctx.calldata
  · intro j hj hne; exact (ctx.allocated j hj hne).trans hm
  · intro j hnext hj hne k hk
    have hw := scheduled_word_above s i
      (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord j) k).toNat (by have hsep := ctx.separated j hj k hk; omega)
    unfold ScheduleCorrect.expectedWord Schedule.readLEWord
    rw [hw]
    exact ctx.messageBlock j (by omega) hj hne k hk
  · by_cases hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i
    · rw [scheduledState_hit s i hh]
      change (MachineState.readWord (StaggerTablePad.padRealResult s.memory _) 0).toNat % 2 ^ 144 < _
      -- `% 2 ^ 144` is bytes 14..31, which `AgreeFrom14` fixes; address 0 itself is not readable
      -- through `AgreeFrom14.readWord`.
      rw [StaggerTablePad.read_zero_mod_of_agree (StaggerTablePad.padRealResult_agree s.memory
        (UInt256.ofNat s.executionEnv.calldata.size) ctx.lowClear)]
      refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
      rw [ctx.calldata] at hh ⊢
      rw [StaggerTablePad.resultMemory_eq_table _ _ (size_word_lt input hfit),
        StaggerTableLayout.read_zero,
        StaggerTablePad.padWordsDirty_ne _ StaggerTableLayout.slots[0]! (by decide) (by decide),
        pad_words input i hfit hh _ (StaggerTableLayout.slots_lt 0 (by decide)),
        Word.ofUInt32_toNat]
      exact (blockWords input i _).toBitVec.isLt
    · rw [scheduledState_miss s i hh]
      have hsplit := StaggerScratch.dirtyWord_split s.memory (messagePointer i) StaggerTableLayout.slots[0]!
      have he := PairedScheduleData.extractedWord_bound s.memory (messagePointer i) StaggerTableLayout.slots[0]!
      have h0 := hsplit.2.2.2 (by decide)
      have hb6 : (selectedWords s i 6).toNat < 2 ^ 32 := by
        have := StaggerScratch.dirtyWord_split s.memory (messagePointer i) 6
        exact Nat.lt_of_div_eq_zero (by norm_num) (this.2.2.2 (by decide))
      change (MachineState.readWord
        (StaggerTableLayout.resultMemory0 s.memory (selectedWords s i)) 0).toNat % 2 ^ 144 < _
      rw [StaggerTableLayout.read_zero0, StaggerTableLayout.dualLane_toNat _ hb6,
        Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.lt_trans hb6 (by norm_num))]
      exact hb6

theorem calldata_lt_uint256 (input : ByteArray) (hfit : CalldataFits input) :
    input.size < 2^256 := by
  unfold CalldataFits at hfit
  omega

theorem messagePointer_aligned (i : Nat) : messagePointer i % 32 = 31 := by
  unfold messagePointer Padding.messageOffset DriverTrace.blockOffset
  omega

theorem blockOffsetWord_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    (DriverTrace.blockOffsetWord i).toNat = DriverTrace.blockOffset i := by
  have hb := messagePointer_bound input hfit i hi
  unfold messagePointer at hb
  rw [DriverTrace.blockOffsetWord, Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem scheduled_active_eq (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input i) :
    (scheduledState s i).activeWords = s.activeWords := by
  by_cases hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i
  · rw [scheduledState_hit s i hh]
  · rw [scheduledState_miss s i hh]
    rw [ctx.calldata] at hh
    exact PairTableActive.loaded_active_eq_of_ceil_allocated s _
      (messagePointer_bound input hfit i hi) (ctx.allocated i hi hh)

theorem scheduled_memory_calldata (s : State) (i : Nat)
    (hhit : s.executionEnv.calldata.size = DriverTrace.blockOffset i) :
    StaggerTablePad.padRealResult s.memory (UInt256.ofNat s.executionEnv.calldata.size) =
      (scheduledState s i).memory := by
  rw [scheduledState_hit s i hhit]

#print axioms ready
#print axioms Context.scheduled
#print axioms scheduled_memory_calldata
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTable
