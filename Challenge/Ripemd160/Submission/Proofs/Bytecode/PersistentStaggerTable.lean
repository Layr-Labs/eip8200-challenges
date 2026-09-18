import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolPadInvariant
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolReference
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
  /-- The actual image's own zero set (`PoolShapeV2.zeroAddressesV2`): sixty band bytes
between 50 and 1044, each `18 * j + k` with `14 ≤ k < 18`.  Nothing below byte 50 is
constrained: the first memory word may carry whatever the raw schedule word 6 drags into
table slot 0. -/
  clear : PoolShapeV2.ClearV2 s.memory

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
    {s with memory := PoolReference.dataMemory s.memory (messagePointer i), activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))}

theorem scheduledState_hit (s : State) (i : Nat)
    (hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i) :
    scheduledState s i =
      {s with memory := StaggerTablePad.padRealResult s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  unfold scheduledState; rw [if_pos hh]

theorem scheduledState_miss (s : State) (i : Nat)
    (hh : ¬ s.executionEnv.calldata.size = DriverTrace.blockOffset i) :
    scheduledState s i =
      {s with memory := PoolReference.dataMemory s.memory (messagePointer i), activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))} := by
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
    -- The real table agrees with the model from byte 28, and slot 1 is carried onto `Safe`.
    apply PoolPadInvariant.pad_ready
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
    apply PoolReference.data_ready _ _ (messagePointer_lower i) ctx.clear
    refine StaggerMessage.ready_dual0 (PoolInvariant.sanitize s.memory)
      (PairedScheduleData.extractedWord s.memory (messagePointer i)) (blockWords input i)
      (PairedScheduleData.extractedWord_bound _ _ 6) ?_
    exact StaggerMessage.ready_junk (PoolInvariant.sanitize s.memory)
      (PairedScheduleData.extractedWord s.memory (messagePointer i)) (blockWords input i)
      (fun _ => 0)
      (fun k hk => by
        rw [extracted_words s input i hfit hi ctx hh k hk, Word.ofUInt32_toNat]
        omega)
      (fun k _ => by norm_num)
      (fun k _ _ => by norm_num)
      (fun k _ _ _ => by norm_num)
        (fun k _ _ => ⟨by norm_num, fun _ => rfl⟩)

theorem scheduled_word_above (s : State) (i address : Nat) (ha : 1120 ≤ address) :
    MachineState.readWord (scheduledState s i).memory address = MachineState.readWord s.memory address := by
  by_cases hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i
  · rw [scheduledState_hit s i hh]
    change MachineState.readWord (StaggerTablePad.padRealResult s.memory _) address = _
    exact StaggerTablePad.read_padRealResult_outside _ _ _ (by omega)
  · rw [scheduledState_miss s i hh]
    exact PoolInvariant.read_resultV2_outside _ _ _ address (by omega)

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

/-- The zero set survives both kinds of block: the data block by `clear_sources`, the
pad-only block because every one of its stores is 18-aligned and below `2 ^ 112`. -/
theorem scheduled_clear (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (ctx : Context s input i) :
    PoolShapeV2.ClearV2 (scheduledState s i).memory := by
  by_cases hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i
  · rw [scheduledState_hit s i hh]
    exact PoolPadInvariant.padRealResult_clear _ _
      (by rw [ctx.calldata]; exact size_word_lt input hfit)
  · rw [scheduledState_miss s i hh]
    exact PoolFacts.result_clear _ _ _ ctx.clear

theorem Context.scheduled (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input i) : Context (scheduledState s i) input (i + 1) := by
  have hm := scheduled_active_mono s input i hfit hi
  refine ⟨?_, ctx.active.trans hm, ?_, ?_, ctx.separated, scheduled_clear s input i hfit ctx⟩
  · rw [scheduled_env]; exact ctx.calldata
  · intro j hj hne; exact (ctx.allocated j hj hne).trans hm
  · intro j hnext hj hne k hk
    have hw := scheduled_word_above s i
      (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord j) k).toNat (by have hsep := ctx.separated j hj k hk; omega)
    unfold ScheduleCorrect.expectedWord Schedule.readLEWord
    rw [hw]
    exact ctx.messageBlock j (by omega) hj hne k hk

theorem calldata_lt_uint256 (input : ByteArray) (hfit : CalldataFits input) :
    input.size < 2^256 := by
  unfold CalldataFits at hfit
  omega

theorem messagePointer_aligned (i : Nat) : messagePointer i % 32 = 0 := by
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
