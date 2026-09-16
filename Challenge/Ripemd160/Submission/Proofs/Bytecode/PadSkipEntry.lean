import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTable
import Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Pool
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
open PairStoreGap

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

/-! ## The first memory word at block-loop entry

Only the calldata copy, the sentinel and the length footer are stored before the block
loop, all at or above the message offset, so the first memory word is still zero. -/

private theorem byteFrom_zero_beyond (bs : ByteArray) (i : Nat) (h : bs.size ≤ i) :
    YulSemantics.EVM.byteFrom bs.toList i = 0 := by
  unfold YulSemantics.EVM.byteFrom
  rw [YulEvmCompiler.ByteArray.toList_eq_data, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]
  exact Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le bs i h

private theorem bytesToNatPadded_zero_beyond (bs : ByteArray) (off : Nat)
    (hoff : bs.size ≤ off) : ∀ n : Nat,
    EvmSemantics.EVM.Precompile.bytesToNatPadded bs off n = 0
  | 0 => Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width bs off
  | n + 1 => by
      rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ,
        bytesToNatPadded_zero_beyond bs off hoff n,
        byteFrom_zero_beyond bs (off + n) (by omega)]
      rfl

private theorem base_readWord (input : ByteArray) :
    MachineState.readWord (PaddingTrace.padLengthReady input).memory 0 = 0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat,
    bytesToNatPadded_zero_beyond _ 0 (by change 0 ≤ 0; exact Nat.le_refl 0) 32]
  rfl

theorem entryState_lowClear (input : ByteArray) (hfit : CalldataFits input) :
    (MachineState.readWord (entryState input).memory 0).toNat < 2 ^ 32 := by
  have hbase := base_readWord input
  unfold entryState PaddingTrace.entryState
  split
  · change (MachineState.readWord (MachineState.writeBytes (PaddingTrace.padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset) 0).toNat < _
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
      (Or.inl (by unfold Padding.messageOffset; omega)), hbase]
    decide
  · rw [PaddingTrace.padReturned_readWord input hfit 0 (by unfold Padding.messageOffset; omega)]
    unfold Padding.paddedMemory Padding.sentinelMemory Padding.copiedMemory
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
        (Or.inl (by unfold Padding.messageOffset; have := (paddedLength_ge input.size).2; omega)),
      Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
        (Or.inl (by unfold Padding.messageOffset; omega)),
      Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
        (Or.inl (by unfold Padding.messageOffset; omega)), hbase]
    decide

theorem entryState_gapClear (input : ByteArray) (hfit : CalldataFits input) :
    GapClear (PadSkipEntry.entryState input).memory := by
  intro j hj k hk0 hk1
  have hjb := lowerPairSlots_bounds j hj
  have ha : 18 * j + k < Padding.messageOffset := by
    unfold Padding.messageOffset
    omega
  have hbase : (PaddingTrace.padLengthReady input).memory = ByteArray.empty := rfl
  have hp : 64 ≤ Padding.paddedLength input.size := by
    unfold Padding.paddedLength
    omega
  unfold PadSkipEntry.entryState PaddingTrace.entryState
  split
  · change (MachineState.writeBytes (PaddingTrace.padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset)[18 * j + k]?.getD 0 = 0
    rw [MachineState.writeBytes_getElem?_getD, if_neg (by omega), hbase]
    simp
  · rw [PaddingTrace.padReturned_getD_window input hfit _ (by omega)]
    simp only [Padding.paddedMemory, Padding.sentinelMemory, Padding.copiedMemory,
      MachineState.writeBytes_getElem?_getD]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hbase]
    simp

/-- Every byte below the message offset is zero at entry. -/
theorem entryState_byte_zero (input : ByteArray) (hfit : CalldataFits input) (a : Nat)
    (ha : a < Padding.messageOffset) :
    (PadSkipEntry.entryState input).memory[a]?.getD 0 = 0 := by
  have hbase : (PaddingTrace.padLengthReady input).memory = ByteArray.empty := rfl
  have hp : 64 ≤ Padding.paddedLength input.size := by
    unfold Padding.paddedLength
    omega
  unfold PadSkipEntry.entryState PaddingTrace.entryState
  split
  · change (MachineState.writeBytes (PaddingTrace.padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset)[a]?.getD 0 = 0
    rw [MachineState.writeBytes_getElem?_getD, if_neg (by omega), hbase]
    simp
  · rw [PaddingTrace.padReturned_getD_window input hfit _ (by omega)]
    simp only [Padding.paddedMemory, Padding.sentinelMemory, Padding.copiedMemory,
      MachineState.writeBytes_getElem?_getD]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hbase]
    simp

/-- The six bytes the unmasked pool loads read are zero at entry. -/
theorem entryState_poolClear (input : ByteArray) (hfit : CalldataFits input) :
    PairStoreGap.PoolClear (PadSkipEntry.entryState input).memory := by
  refine ⟨?_, ?_, ?_⟩ <;>
    exact JD8Pool.window2_of_bytes _ _
      (entryState_byte_zero input hfit _ (by unfold Padding.messageOffset; omega))
      (entryState_byte_zero input hfit _ (by unfold Padding.messageOffset; omega))

#print axioms entryState_poolClear
#print axioms entryState_gapClear
#print axioms entryState_lowClear
#print axioms entryState_active
#print axioms entryState_allocated
#print axioms entryState_blockAt
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadSkipEntry
