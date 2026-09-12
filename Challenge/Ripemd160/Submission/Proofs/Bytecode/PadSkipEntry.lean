import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTable
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
/-!
# Block-loop entry after the whole-block padding skip

For a length that is a multiple of 64 the padding code leaves only the calldata copy in
memory and enters the block loop directly; its last block is the pad-only block, which is
scheduled from the constant table and never reads message memory.  Otherwise the sentinel
and the length footer are written as before.  This file states the block-model context
facts for both entry states.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadSkipEntry
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM

abbrev entryState (input : ByteArray) : State := PaddingTrace.entryState input

theorem entryState_halt (input : ByteArray) : (entryState input).halt = .Running := by
  unfold entryState PaddingTrace.entryState
  split <;> rfl

theorem entryState_callStack (input : ByteArray) : (entryState input).callStack = [] := by
  unfold entryState PaddingTrace.entryState
  split <;> rfl

theorem entryState_calldata (input : ByteArray) :
    (entryState input).executionEnv.calldata = input := by
  unfold entryState PaddingTrace.entryState
  split <;> rfl

theorem entryState_code (input : ByteArray) :
    (entryState input).executionEnv.code = submissionBytecode := by
  unfold entryState PaddingTrace.entryState
  split <;> rfl

theorem entryState_fork (input : ByteArray) : (entryState input).executionEnv.fork = .Osaka := by
  unfold entryState PaddingTrace.entryState
  split <;> rfl

theorem entryState_noPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig (entryState input).executionEnv.precompileConfig
      (entryState input).executionEnv.fork (entryState input).executionEnv.codeAddr = false := by
  unfold entryState PaddingTrace.entryState
  split
  · exact deployAddress_not_precompile
  · exact deployAddress_not_precompile

private theorem paddedLength_ge (n : Nat) : n + 9 ≤ Padding.paddedLength n ∧ 64 ≤ Padding.paddedLength n := by
  unfold Padding.paddedLength
  omega

/-- The skip state's high-water mark covers the whole calldata copy. -/
private theorem skip_active_toNat (input : ByteArray) (hfit : CalldataFits input)
    (hpos : 0 < input.size) :
    (Padding.messageOffset + input.size - 1) / 32 + 1 ≤
      (PaddingTrace.padSkip input).activeWords.toNat := by
  have hsize : input.size < 2 ^ 64 := hfit
  have hcur : (PaddingTrace.padLengthReady input).activeWords.toNat < 2 ^ 256 :=
    (PaddingTrace.padLengthReady input).activeWords.val.isLt
  change _ ≤ (UInt256.ofNat (MachineState.activeWordsAfter
    (PaddingTrace.padLengthReady input).activeWords.toNat Padding.messageOffset input.size)).toNat
  unfold MachineState.activeWordsAfter
  rw [if_neg (by omega)]
  dsimp only
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
  · exact Nat.le_max_right _ _
  · rw [Nat.max_lt]
    refine ⟨hcur, ?_⟩
    unfold Padding.messageOffset
    have : (2:Nat) ^ 64 < 2 ^ 256 := by norm_num
    omega

theorem entryState_active (input : ByteArray) (hfit : CalldataFits input)
    (hpos : 0 < input.size) : 37 ≤ (entryState input).activeWords.toNat := by
  unfold entryState PaddingTrace.entryState
  split
  · next hz =>
    have h := skip_active_toNat input hfit hpos
    have h64 : 64 ≤ input.size := by omega
    unfold Padding.messageOffset at h
    omega
  · have h := PaddingTrace.padReturned_allocated input hfit
    have hl := (paddedLength_ge input.size).2
    unfold Padding.messageOffset at h
    omega

theorem entryState_allocated (input : ByteArray) (hfit : CalldataFits input) :
    ∀ i, i < DriverTrace.blockCount input → input.size ≠ DriverTrace.blockOffset i →
      (PersistentStaggerTable.messagePointer i + 64) / 32 ≤ (entryState input).activeWords.toNat := by
  intro i hi hne
  unfold entryState PaddingTrace.entryState
  simp only [PersistentStaggerTable.messagePointer, Padding.messageOffset]
  split
  · next hz =>
    unfold DriverTrace.blockCount Padding.paddedLength at hi
    unfold DriverTrace.blockOffset at hne ⊢
    have hpos : 0 < input.size := by omega
    have h := skip_active_toNat input hfit hpos
    unfold Padding.messageOffset at h
    omega
  · have h := PaddingTrace.padReturned_allocated input hfit
    have heq := Padding.paddedLength_eq_blocks input.size
    unfold Padding.messageOffset at h
    unfold DriverTrace.blockCount at hi
    unfold DriverTrace.blockOffset
    omega

/-- Below the end of the input the skip memory agrees with the one-pass padded image. -/
private theorem skip_getD (input : ByteArray) (a : Nat)
    (ha : a < Padding.messageOffset + input.size) :
    (PaddingTrace.padSkip input).memory[a]?.getD 0 =
      (Padding.paddedMemory (PaddingTrace.padLengthReady input).memory input)[a]?.getD 0 := by
  have hL := (paddedLength_ge input.size).1
  rw [Padding.paddedMemory, MachineState.writeBytes_getElem?_getD,
    if_neg (by intro h; obtain ⟨h1, _⟩ := h; omega),
    Padding.sentinelMemory, MachineState.writeBytes_getElem?_getD,
    if_neg (by intro h; obtain ⟨h1, _⟩ := h; omega),
    Padding.copiedMemory]
  change (MachineState.writeBytes (PaddingTrace.padLengthReady input).memory
    (MachineState.readPadded input 0 input.size) Padding.messageOffset)[a]?.getD 0 = _
  rw [Challenge.EvmProof.Memory.readPadded_zero_size]

theorem entryState_blockAt (input : ByteArray) (hfit : CalldataFits input) :
    ∀ i, i < DriverTrace.blockCount input → input.size ≠ DriverTrace.blockOffset i →
      ScheduleCorrect.MessageBlockAt (entryState input).memory (DriverTrace.messageOffsetWord i)
        (Padding.paddedMessage input) (DriverTrace.blockOffset i) := by
  intro i hi hne
  have heq := Padding.paddedLength_eq_blocks input.size
  unfold entryState PaddingTrace.entryState
  split
  · next hz =>
    have hblk : DriverTrace.blockOffset i + 64 ≤ input.size := by
      unfold DriverTrace.blockCount Padding.paddedLength at hi
      unfold DriverTrace.blockOffset at hne ⊢
      omega
    have hL := (paddedLength_ge input.size).1
    apply PaddedBlockBridge.paddedBlockAt (PaddingTrace.padSkip input)
      (PaddingTrace.padLengthReady input).memory input
    · intro a _ ha
      exact skip_getD input a (by omega)
    · change 0 ≤ Padding.messageOffset
      exact Nat.zero_le _
    · rfl
    · exact hfit
    · omega
  · have hi' : i < Padding.paddedLength input.size / 64 := hi
    exact PaddedBlockBridge.padReturned_blockIndexAt input hfit i hi'

#print axioms entryState_active
#print axioms entryState_allocated
#print axioms entryState_blockAt
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadSkipEntry
