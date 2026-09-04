import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionFunctionalTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

/-!
# H09 immediate-frame facts

These facts expose the active-memory and functional seams after the H09
schedule and copy frame.  The executable frame remains in `ImmediateFrame`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateFrameFacts

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open ImmediateFrame
open CompressionTrace

private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    apply Nat.max_eq_left
    have hq : (offset + size - 1) / 32 < curr :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

private theorem activeWordsAfterUInt256_2_eq (s : State)
    (off₁ size₁ off₂ size₂ : Nat)
    (hend₁ : off₁ + size₁ ≤ s.activeWords.toNat * 32)
    (hend₂ : off₂ + size₂ ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256_2 off₁ size₁ off₂ size₂ = s.activeWords := by
  unfold State.activeWordsAfterUInt256_2
  rw [activeWordsAfter_eq_of_end_le _ _ _ hend₁,
    activeWordsAfter_eq_of_end_le _ _ _ hend₂]
  cases s.activeWords with
  | mk val => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]

private theorem copyRegion_activeWords_neutral (s : State) (dest src size : Nat)
    (hdest : dest + size ≤ s.activeWords.toNat * 32)
    (hsrc : src + size ≤ s.activeWords.toNat * 32) :
    (CompressionTrace.copyRegion s dest src size).activeWords = s.activeWords := by
  unfold CompressionTrace.copyRegion
  exact activeWordsAfterUInt256_2_eq s dest size src size hdest hsrc

private theorem copiedWorkingState_activeWords_neutral (s : State)
    (hactive : 21 ≤ s.activeWords.toNat) :
    (CompressionTrace.copiedWorkingState s).activeWords = s.activeWords := by
  let q₁ := CompressionTrace.copyRegion s 192 32 160
  let q₂ := CompressionTrace.copyRegion q₁ 352 32 160
  have h₁ : q₁.activeWords = s.activeWords := by
    apply copyRegion_activeWords_neutral <;> omega
  have h₂ : q₂.activeWords = s.activeWords := by
    exact (copyRegion_activeWords_neutral q₁ 352 32 160
      (by rw [h₁]; omega) (by rw [h₁]; omega)).trans h₁
  unfold CompressionTrace.copiedWorkingState
  exact (copyRegion_activeWords_neutral q₂ 512 32 160
    (by rw [h₂]; omega) (by rw [h₂]; omega)).trans h₂

theorem prologuefirstWrapperEntry_activeWords_ge67 (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat)
    (hblock : i < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) :
    67 ≤ (firstWrapperEntry s (DriverTrace.messageOffsetWord i)
      returnDest rest).activeWords.toNat := by
  have hsched :
      (scheduledStateH09 s (DriverTrace.messageOffsetWord i) returnDest rest).activeWords.toNat =
        max s.activeWords.toNat (67 + 2 * i) := by
    simpa [scheduledStateH09] using
      (ScheduleActiveWords.scheduledState_activeWords s input hfit i hblock
        (UInt256.ofNat 0x72f)
        (DriverTrace.messageOffsetWord i :: returnDest :: rest))
  have hsched67 :
      67 ≤ (scheduledStateH09 s (DriverTrace.messageOffsetWord i) returnDest rest).activeWords.toNat := by
    rw [hsched]
    exact (by omega : 67 ≤ 67 + 2 * i).trans (Nat.le_max_right _ _)
  have hreturned67 :
      67 ≤ (scheduleReturnedH09 s (DriverTrace.messageOffsetWord i)
        returnDest rest).activeWords.toNat := by
    simpa [scheduleReturnedH09, Schedule.scheduleReturned] using hsched67
  have hcopy :
      (CompressionTrace.copiedWorkingState
        (scheduleReturnedH09 s (DriverTrace.messageOffsetWord i) returnDest rest)).activeWords =
        (scheduleReturnedH09 s (DriverTrace.messageOffsetWord i) returnDest rest).activeWords := by
    apply copiedWorkingState_activeWords_neutral
    omega
  change 67 ≤
    (CompressionTrace.copiedWorkingState
      (scheduleReturnedH09 s (DriverTrace.messageOffsetWord i) returnDest rest)).activeWords.toNat
  rw [hcopy]
  exact hreturned67

theorem prologueFirstWrapperEntry_activeWords_ge67 (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat)
    (hblock : i < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) :
    67 ≤ (firstWrapperEntry s (DriverTrace.messageOffsetWord i)
      returnDest rest).activeWords.toNat :=
  prologuefirstWrapperEntry_activeWords_ge67 s input hfit i hblock returnDest rest

theorem firstWrapperEntry_tables (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (htables : InitializationCorrect.TablesCorrect s.memory) :
    InitializationCorrect.TablesCorrect
      (firstWrapperEntry s messageOffset returnDest rest).memory := by
  rw [firstWrapperEntry_normalized]
  change InitializationCorrect.TablesCorrect
    (CompressionTrace.leftInitialState s messageOffset returnDest rest).memory
  rcases htables with ⟨hr, hrP, hs, hsP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (CompressionTrace.leftInitialState s messageOffset returnDest rest)
        (0x4a0 + 32 * (i / 32))) = _
    rw [CompressionFunctionalTrace.leftInitialState_words s messageOffset returnDest rest
      (0x4a0 + 32 * (i / 32)) (by omega)]
    exact hr i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (CompressionTrace.leftInitialState s messageOffset returnDest rest)
        (0x500 + 32 * (i / 32))) = _
    rw [CompressionFunctionalTrace.leftInitialState_words s messageOffset returnDest rest
      (0x500 + 32 * (i / 32)) (by omega)]
    exact hrP i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (CompressionTrace.leftInitialState s messageOffset returnDest rest)
        (0x560 + 32 * (i / 32))) = _
    rw [CompressionFunctionalTrace.leftInitialState_words s messageOffset returnDest rest
      (0x560 + 32 * (i / 32)) (by omega)]
    exact hs i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (CompressionTrace.leftInitialState s messageOffset returnDest rest)
        (0x5c0 + 32 * (i / 32))) = _
    rw [CompressionFunctionalTrace.leftInitialState_words s messageOffset returnDest rest
      (0x5c0 + 32 * (i / 32)) (by omega)]
    exact hsP i hi

theorem firstWrapperEntry_constants (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hconstants :
      (∀ j, j < 5 →
        InitializationCorrect.slotWord s.memory 0x620 j =
          Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!)) ∧
      (∀ j, j < 5 →
        InitializationCorrect.slotWord s.memory 0x6c0 j =
          Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))) :
    (∀ j, j < 5 →
      InitializationCorrect.slotWord
          (firstWrapperEntry s messageOffset returnDest rest).memory 0x620 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!)) ∧
    (∀ j, j < 5 →
      InitializationCorrect.slotWord
          (firstWrapperEntry s messageOffset returnDest rest).memory 0x6c0 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!)) := by
  rw [firstWrapperEntry_normalized]
  change (∀ j, j < 5 →
      InitializationCorrect.slotWord
          (CompressionTrace.leftInitialState s messageOffset returnDest rest).memory 0x620 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!)) ∧
    (∀ j, j < 5 →
      InitializationCorrect.slotWord
          (CompressionTrace.leftInitialState s messageOffset returnDest rest).memory 0x6c0 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))
  rcases hconstants with ⟨hk, hkP⟩
  refine ⟨?_, ?_⟩
  · intro j hj
    unfold InitializationCorrect.slotWord
    change wordAt (CompressionTrace.leftInitialState s messageOffset returnDest rest)
      (0x620 + 32 * j) = _
    rw [CompressionFunctionalTrace.leftInitialState_words s messageOffset returnDest rest
      (0x620 + 32 * j) (by omega)]
    exact hk j hj
  · intro j hj
    unfold InitializationCorrect.slotWord
    change wordAt (CompressionTrace.leftInitialState s messageOffset returnDest rest)
      (0x6c0 + 32 * j) = _
    rw [CompressionFunctionalTrace.leftInitialState_words s messageOffset returnDest rest
      (0x6c0 + 32 * j) (by omega)]
    exact hkP j hj

theorem firstWrapperEntry_initialLaneInvariant (word : Nat → UInt32)
    (s : State) (messageOffset returnDest : UInt256) (rest : List UInt256) :
    CompressionTrace.LeftInvariant word
      (CompressionTrace.workingAt
        (CompressionTrace.leftInitialState s messageOffset returnDest rest) 192) 0
      (CompressionTrace.workingAt
        (firstWrapperEntry s messageOffset returnDest rest) 192) := by
  rw [firstWrapperEntry_normalized]
  change CompressionTrace.LeftInvariant word
      (CompressionTrace.workingAt
        (CompressionTrace.leftInitialState s messageOffset returnDest rest) 192) 0
      (CompressionTrace.workingAt
        (CompressionTrace.leftInitialState s messageOffset returnDest rest) 192)
  exact CompressionTrace.leftInvariant_zero word _

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateFrameFacts
