import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableActive
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableCongruence
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlyContract
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTable
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof

structure Context (s : State) (input : ByteArray) : Prop where
  calldata : s.executionEnv.calldata = input
  allocated : (PaddingTrace.padReturned input).activeWords.toNat ≤ s.activeWords.toNat
  messageBlock : ∀ i, i < DriverTrace.blockCount input →
    ScheduleCorrect.MessageBlockAt s.memory (DriverTrace.messageOffsetWord i)
      (Padding.paddedMessage input) (DriverTrace.blockOffset i)
  separated : ∀ i, i < DriverTrace.blockCount input → ∀ k, k < 16 →
    1024 ≤ (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord i) k).toNat

def messagePointer (i : Nat) : Nat := Padding.messageOffset + DriverTrace.blockOffset i

def blockWords (input : ByteArray) (i : Nat) : Nat → UInt32 :=
  fun k => (CompressionCorrect.schedule (Padding.paddedMessage input)
    (DriverTrace.blockOffset i))[k]!

theorem blockWords_eq_readLE32 (input : ByteArray) (i k : Nat) (hk : k < 16) :
    blockWords input i k = Crypto.Ripemd160.readLE32 (Padding.paddedMessage input)
      (DriverTrace.blockOffset i + k * 4) := by
  interval_cases k <;> simp [blockWords, CompressionCorrect.schedule, List.range']

theorem messagePointer_lower (i : Nat) : 1024 ≤ messagePointer i := by
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
  PairedScheduleData.extractedWord s.memory (messagePointer i)

def scheduledState (s : State) (i : Nat) : State :=
  {s with memory := StaggerTableLayout.resultMemory s.memory (selectedWords s i), activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))}

theorem scheduled_active (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) :
    34 ≤ (scheduledState s i).activeWords.toNat :=
  PairTableActive.loaded_active_ge34 s (messagePointer i)
    (messagePointer_lower i) (messagePointer_bound input hfit i hi)

theorem extracted_words (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input) (k : Nat) (hk : k < 16) :
    selectedWords s i k = Word.ofUInt32 (blockWords input i k) := by
  rw [selectedWords, PairedScheduleData.extractedWord_eq_expectedWord _ _ _ hk
    (messagePointer_bound input hfit i hi)]
  change ScheduleCorrect.expectedWord s.memory (DriverTrace.messageOffsetWord i) k = _
  rw [ctx.messageBlock i hi k hk, blockWords_eq_readLE32 input i k hk]

theorem ready (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input) :
    StaggerMessage.Ready (scheduledState s i).memory (blockWords input i) :=
  StaggerMessage.ready s.memory (selectedWords s i) (blockWords input i)
    (extracted_words s input i hfit hi ctx)

theorem scheduled_word_above (s : State) (i address : Nat) (ha : 1024 ≤ address) :
    MachineState.readWord (scheduledState s i).memory address = MachineState.readWord s.memory address :=
  StaggerTableLayout.read_resultMemory_outside _ _ _ (by omega)

theorem Context.scheduled (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input) : Context (scheduledState s i) input := by
  refine ⟨ctx.calldata, ?_, ?_, ctx.separated⟩
  · exact ctx.allocated.trans (PairTableActive.loaded_active_mono s (messagePointer i)
      (messagePointer_bound input hfit i hi))
  · intro j hj k hk
    have hw := scheduled_word_above s i
      (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord j) k).toNat (ctx.separated j hj k hk)
    unfold ScheduleCorrect.expectedWord Schedule.readLEWord
    rw [hw]
    exact ctx.messageBlock j hj k hk

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
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input) :
    DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i)) = s.activeWords := by
  apply PairTableActive.loaded_active_eq_of_allocated s _
    (messagePointer_bound input hfit i hi) (messagePointer_aligned i)
  have hpad := PaddingTrace.padReturned_allocated input hfit
  have hlength := DriverTrace.paddedLength_eq_blockCount input
  have hctx := ctx.allocated
  unfold messagePointer DriverTrace.blockOffset Padding.messageOffset at *
  omega

theorem scheduled_memory_calldata (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input)
    (hhit : input.size = DriverTrace.blockOffset i) :
    StaggerTablePad.resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size) =
      (scheduledState s i).memory := by
  rw [ctx.calldata, StaggerTablePad.resultMemory_eq_table]
  apply StaggerTableLayout.resultMemory_congr
  intro k hk
  symm
  apply PadOnlySchedule.extracted_words s.memory input (messagePointer i)
    hfit (by rw [hhit, DriverTrace.blockOffset]; omega)
    (messagePointer_bound input hfit i hi) _ k hk
  rw [hhit]
  exact ctx.messageBlock i hi

#print axioms ready
#print axioms Context.scheduled
#print axioms scheduled_memory_calldata
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTable
