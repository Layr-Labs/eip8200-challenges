import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessSpread
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleMemory

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessValues

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- The selected 32-bit window of a memory word is exactly its four source
bytes, including zero padding. No memory-size premise is hidden here. -/
theorem masked_window (memory : ByteArray) (offset j : Nat) (hj : j < 8) :
    (Word.mask32 (PackedScheduleMath.shr (MachineState.readWord memory offset)
      (32 * (7 - j)))).toNat =
      Precompile.bytesToNatPadded memory (offset + 4 * j) 4 := by
  rw [Word.mask32_toNat]
  unfold PackedScheduleMath.shr
  rw [Word.shiftRight_toNat _ (by omega)]
  have hwidth : 4 * j + 4 ≤ 32 := by omega
  have hshift : 32 * (7 - j) = (32 - (4 * j + 4)) * 8 := by omega
  rw [hshift, Bytes.readWord_shift_toNat memory offset (4 * j + 4) hwidth]
  rw [Bytes.bytesToNatPadded_add memory offset (4 * j) 4]
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  have hsmall := Bytes.bytesToNatPadded_lt_pow memory (offset + 4 * j) 4
  rw [show 256 ^ 4 = 2 ^ 32 by norm_num] at hsmall ⊢
  simpa [Nat.add_mod] using Nat.mod_eq_of_lt hsmall

#print axioms masked_window

theorem spreadValue_toNat (memory : ByteArray) (i : Nat) :
    (PackedPreprocessLayout.spreadValue memory i).toNat =
      PackedPreprocessSpread.lowFour memory i := by
  change (Word.mask32 (MachineState.readWord memory
    (PackedPreprocessLayout.sourceAddress i))).toNat = _
  rw [Word.mask32_eq_ofUInt32, Word.ofUInt32_toNat,
    PackedPreprocessSpread.toUInt32_readWord_eq_lowFour,
    Word.toUInt32_toNat, Word.word_toNat_ofNat]
  have hsmall := Bytes.bytesToNatPadded_lt_pow memory
    (PackedPreprocessLayout.sourceAddress i + 28) 4
  change PackedPreprocessSpread.lowFour memory i < 256 ^ 4 at hsmall
  have h32 : PackedPreprocessSpread.lowFour memory i < 2 ^ 32 := by
    simpa using hsmall
  rw [Nat.mod_eq_of_lt (h32.trans (by norm_num)), Nat.mod_eq_of_lt h32]

/-- Relate the unaligned source load used by each emitted spread group to
the corresponding four-byte window of the two aligned byte-swapped words. -/
theorem spreadValue_aligned_window (memory : ByteArray) (i : Nat) :
    (PackedPreprocessLayout.spreadValue memory i).toNat =
      (Word.mask32 (PackedScheduleMath.shr
        (MachineState.readWord memory (288 + 32 * (i / 8)))
        (32 * (7 - i % 8)))).toNat := by
  rw [spreadValue_toNat, masked_window memory _ _ (Nat.mod_lt _ (by decide))]
  unfold PackedPreprocessSpread.lowFour
  rw [PackedPreprocessLayout.source_tail_address]
  congr 1
  have hdiv := Nat.div_add_mod i 8
  omega

#print axioms spreadValue_aligned_window

/-- Once the two aligned stores are established by the byte-swap trace, all
sixteen spread operands are the specified little-endian message words. -/
theorem spreadValue_eq_expected (memory inputMemory : ByteArray) (source i : Nat)
    (hi : i < 16) (hbound : source + 64 < 2 ^ 256)
    (hwords : ∀ half, half < 2 →
      MachineState.readWord memory (288 + 32 * half) =
        PackedScheduleMath.packed
          (MachineState.readWord inputMemory (source + 32 * half))) :
    PackedPreprocessLayout.spreadValue memory i =
      ScheduleCorrect.expectedWord inputMemory
        (PackedScheduleMemory.naturalp source) i := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hhalf : i / 8 < 2 := by omega
  have hsource : source + 32 * (i / 8) + 4 * (i % 8) = source + 4 * i := by
    have hdiv := Nat.div_add_mod i 8
    omega
  have hbase : PackedScheduleMath.le4
      (MachineState.readWord inputMemory (source + 32 * (i / 8))) (i % 8) =
      Schedule.readLEWord inputMemory
        (Schedule.loadOffsetWord (PackedScheduleMemory.naturalp source) i) := by
    rw [PackedScheduleMath.le4_readWord_offset inputMemory _ _ hj, hsource]
    unfold Schedule.readLEWord
    rw [PackedScheduleMemory.loadOffsetWord_toNat source i hi hbound]
    rfl
  apply Word.word_ext
  rw [spreadValue_aligned_window, hwords (i / 8) hhalf,
    PackedScheduleMath.packed_extract _ _ hj, hbase]
  rfl

#print axioms spreadValue_eq_expected

theorem packedBaseMemory_read0 (memory : ByteArray) (word0 word1 : UInt256) :
    MachineState.readWord
      (PackedPreprocessLayout.packedBaseMemory memory word0 word1) 288 =
        PackedScheduleMath.packed word0 := by
  unfold PackedPreprocessLayout.packedBaseMemory PackedGapInvariant.storeWord
  exact Memory.readWord_writeWord _ _ _

theorem packedBaseMemory_read1 (memory : ByteArray) (word0 word1 : UInt256) :
    MachineState.readWord
      (PackedPreprocessLayout.packedBaseMemory memory word0 word1) 320 =
        PackedScheduleMath.packed word1 := by
  unfold PackedPreprocessLayout.packedBaseMemory PackedGapInvariant.storeWord
  rw [Memory.readWord_writeBytes_disjoint]
  · exact Memory.readWord_writeWord _ _ _
  · right
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]

/-- Discharge the aligned-word premise with the actual preprocessing memory
model. This supplies the sixteen operand identities needed by compression. -/
theorem spreadValue_packedBaseMemory (memory : ByteArray) (source i : Nat)
    (hi : i < 16) (hbound : source + 64 < 2 ^ 256) :
    PackedPreprocessLayout.spreadValue
      (PackedPreprocessLayout.packedBaseMemory memory
        (MachineState.readWord memory source)
        (MachineState.readWord memory (source + 32))) i =
      ScheduleCorrect.expectedWord memory
        (PackedScheduleMemory.naturalp source) i := by
  apply spreadValue_eq_expected _ memory source i hi hbound
  intro half hhalf
  interval_cases half
  · simpa using packedBaseMemory_read0 memory
      (MachineState.readWord memory source)
      (MachineState.readWord memory (source + 32))
  · simpa using packedBaseMemory_read1 memory
      (MachineState.readWord memory source)
      (MachineState.readWord memory (source + 32))

#print axioms spreadValue_packedBaseMemory

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessValues
