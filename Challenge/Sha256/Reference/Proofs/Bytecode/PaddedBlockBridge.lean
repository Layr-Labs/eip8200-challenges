import Challenge.Sha256.Reference.Proofs.Bytecode.ScheduleCorrect

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Padded-memory bridge for the reference schedule

This file discharges the concrete caller-side seam of `ScheduleCorrect`:
the 32-byte EVM load followed by `SHR 224` reads the same four bytes as the
pinned SHA-256 specification's `readBE32`.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.PaddedBlockBridge

open EvmSemantics
open EvmSemantics.Crypto
open EvmSemantics.EVM

private theorem shl8_eq_mul256 (w : UInt32) : w <<< 8 = w * 256 := by
  apply UInt32.ext
  simp [UInt32.toNat_shiftLeft, UInt32.toNat_mul, Nat.shiftLeft_eq]

private theorem mul256_or_byte (w : UInt32) (b : UInt8) :
    w * 256 ||| b.toUInt32 = w * 256 + b.toUInt32 := by
  apply UInt32.toBitVec_inj.1
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_add]
  symm
  apply BitVec.add_eq_or_of_and_eq_zero
  rw [← shl8_eq_mul256]
  simp only [UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32]
  ext i hi
  by_cases hi8 : i < 8
  · simp [hi8]
  · simp [hi8, BitVec.getLsbD_of_ge b.toBitVec i (by omega)]

private theorem readBE32_eq_bytes (bs : ByteArray) (off : Nat) :
    Sha256.readBE32 bs off = UInt32.ofNat
      (((((bs[off]?.getD 0).toNat * 256 +
          (bs[off + 1]?.getD 0).toNat) * 256 +
          (bs[off + 2]?.getD 0).toNat) * 256) +
        (bs[off + 3]?.getD 0).toNat) := by
  by_cases h0 : off < bs.size
  all_goals by_cases h1 : off + 1 < bs.size
  all_goals by_cases h2 : off + 2 < bs.size
  all_goals by_cases h3 : off + 3 < bs.size
  all_goals try omega
  all_goals
    simp [Sha256.readBE32, Std.Legacy.Range.forIn_eq_forIn_range', List.range',
      h0, h1, h2, h3, shl8_eq_mul256, mul256_or_byte]

private theorem readPadded_four_eq (bs : ByteArray) (off : Nat) :
    MachineState.readPadded bs off 4 = ByteArray.mk #[
      bs[off]?.getD 0, bs[off + 1]?.getD 0,
      bs[off + 2]?.getD 0, bs[off + 3]?.getD 0] := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    rfl
  · intro i hi₁ hi₂
    have hi : i < 4 := by simpa using hi₁
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
    interval_cases i <;> rfl

private theorem bytesToBigEndianNat_readPadded_four (bs : ByteArray)
    (off : Nat) :
    Data.Bytes.bytesToBigEndianNat (MachineState.readPadded bs off 4) =
      ((((bs[off]?.getD 0).toNat * 256 +
          (bs[off + 1]?.getD 0).toNat) * 256 +
          (bs[off + 2]?.getD 0).toNat) * 256) +
        (bs[off + 3]?.getD 0).toNat := by
  rw [readPadded_four_eq]
  simp [Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data]

private theorem readBE32_eq_readPadded (bs : ByteArray) (off : Nat) :
    Sha256.readBE32 bs off = UInt32.ofNat
      (Data.Bytes.bytesToBigEndianNat (MachineState.readPadded bs off 4)) := by
  rw [readBE32_eq_bytes, bytesToBigEndianNat_readPadded_four]

private theorem readPadded_thirtyTwo_split (bs : ByteArray) (off : Nat) :
    MachineState.readPadded bs off 32 =
      MachineState.readPadded bs off 4 ++
        MachineState.readPadded bs (off + 4) 28 := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    have hi : i < 32 := by simpa using hi₁
    rw [if_pos hi, Challenge.EvmProof.Memory.getElem?_getD_append]
    simp only [Challenge.EvmProof.Memory.readPadded_size]
    by_cases h4 : i < 4
    · rw [if_pos h4,
        Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos h4]
    · rw [if_neg h4,
        Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (by omega)]
      congr 2
      omega

private theorem foldl_bytes (xs : List UInt8) (acc : Nat) :
    xs.foldl (fun n b => n * 256 + b.toNat) acc =
      acc * 256 ^ xs.length +
        xs.foldl (fun n b => n * 256 + b.toNat) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [ih (acc * 256 + x.toNat), ih x.toNat, Nat.pow_succ]
      ring

private theorem bytesToBigEndianNat_append (a b : ByteArray) :
    Data.Bytes.bytesToBigEndianNat (a ++ b) =
      Data.Bytes.bytesToBigEndianNat a * 256 ^ b.size +
        Data.Bytes.bytesToBigEndianNat b := by
  unfold Data.Bytes.bytesToBigEndianNat
  rw [Challenge.EvmProof.Bytecode.toList_eq_data,
    Challenge.EvmProof.Bytecode.toList_eq_data,
    Challenge.EvmProof.Bytecode.toList_eq_data]
  rw [ByteArray.data_append, Array.toList_append, List.foldl_append,
    foldl_bytes]
  rfl

private theorem foldl_bytes_lt (xs : List UInt8) :
    xs.foldl (fun n b => n * 256 + b.toNat) 0 < 256 ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, foldl_bytes]
      rw [List.length_cons, Nat.pow_succ]
      simp only [Nat.zero_mul, Nat.zero_add]
      have hx : x.toNat < 256 := x.toNat_lt
      calc
        x.toNat * 256 ^ xs.length +
            List.foldl (fun n b => n * 256 + b.toNat) 0 xs <
            x.toNat * 256 ^ xs.length + 256 ^ xs.length :=
          Nat.add_lt_add_left ih _
        _ = (x.toNat + 1) * 256 ^ xs.length := by ring
        _ ≤ 256 * 256 ^ xs.length :=
          Nat.mul_le_mul_right (256 ^ xs.length) (by omega)
        _ = 256 ^ xs.length * 256 := by omega

private theorem bytesToBigEndianNat_lt (bs : ByteArray) :
    Data.Bytes.bytesToBigEndianNat bs < 256 ^ bs.size := by
  unfold Data.Bytes.bytesToBigEndianNat
  rw [Challenge.EvmProof.Bytecode.toList_eq_data]
  simpa using foldl_bytes_lt bs.data.toList

/-- An EVM `MLOAD` followed by `SHR 224` is exactly the specification's
four-byte big-endian reader, embedded in the low 32 bits of an EVM word. -/
theorem shiftRight_readWord_224 (bs : ByteArray) (off : Nat) :
    UInt256.shiftRight (MachineState.readWord bs off) (UInt256.ofNat 224) =
      Challenge.EvmProof.Word.ofUInt32 (Sha256.readBE32 bs off) := by
  let first := Data.Bytes.bytesToBigEndianNat
    (MachineState.readPadded bs off 4)
  let rest := Data.Bytes.bytesToBigEndianNat
    (MachineState.readPadded bs (off + 4) 28)
  have hfirst : first < 256 ^ 4 := by
    simpa [first] using bytesToBigEndianNat_lt
      (MachineState.readPadded bs off 4)
  have hrest : rest < 256 ^ 28 := by
    simpa [rest] using bytesToBigEndianNat_lt
      (MachineState.readPadded bs (off + 4) 28)
  have hsplit : Data.Bytes.bytesToBigEndianNat
      (MachineState.readPadded bs off 32) = first * 256 ^ 28 + rest := by
    rw [readPadded_thirtyTwo_split, bytesToBigEndianNat_append]
    simp [first, rest]
  have hvalue : Data.Bytes.bytesToBigEndianNat
      (MachineState.readPadded bs off 32) < 2 ^ 256 := by
    rw [hsplit]
    have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
    have hcombine : first * 256 ^ 28 + rest < 256 ^ 32 := by
      have hpowSplit : (256 : Nat) ^ 32 = 256 ^ 4 * 256 ^ 28 := by ring
      rw [hpowSplit]
      omega
    omega
  unfold MachineState.readWord
  rw [Challenge.EvmProof.Word.shiftRight_ofNat hvalue (by omega)]
  rw [hsplit, Nat.shiftRight_eq_div_pow]
  have hpow224 : (2 : Nat) ^ 224 = 256 ^ 28 := by norm_num
  rw [hpow224]
  have hquot : (first * 256 ^ 28 + rest) / 256 ^ 28 = first := by
    calc
      (first * 256 ^ 28 + rest) / 256 ^ 28 =
          first + rest / 256 ^ 28 := by
        rw [Nat.mul_comm first (256 ^ 28),
          Nat.mul_add_div (by positivity)]
      _ = first := by rw [Nat.div_eq_of_lt hrest, Nat.add_zero]
  rw [hquot, readBE32_eq_readPadded]
  unfold Challenge.EvmProof.Word.ofUInt32
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt32.toNat_ofNat']
  have hpow32 : (2 : Nat) ^ 32 = 256 ^ 4 := by norm_num
  rw [hpow32, Nat.mod_eq_of_lt hfirst]

/-- Reading after the message base in the concrete padded memory is the same
zero-padded byte window as reading at the corresponding relative offset in
the padded message itself. -/
theorem readPadded_paddedMemory_shift (base input : ByteArray)
    (off width : Nat) (hbase : base.size ≤ Padding.messageOffset) :
    MachineState.readPadded (Padding.paddedMemory base input)
        (Padding.messageOffset + off) width =
      MachineState.readPadded (Padding.paddedMessage input) off width := by
  rw [Padding.paddedMemory_eq_write base input hbase]
  apply ByteArray.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    have hi : i < width := by simpa using hi₁
    rw [if_pos hi, if_pos hi]
    rw [MachineState.writeBytes_getElem?_getD]
    simp only [Padding.paddedMessage_size]
    by_cases hpadded : off + i < Padding.paddedLength input.size
    · rw [if_pos (by omega)]
      apply congrArg (fun n : Nat =>
        (Padding.paddedMessage input)[n]?.getD 0)
      omega
    · rw [if_neg (by omega)]
      rw [Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le base _
        (by omega)]
      exact (Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le
        (Padding.paddedMessage input) (off + i) (by
          rw [Padding.paddedMessage_size]
          omega)).symm

theorem readWord_paddedMemory_shift (base input : ByteArray) (off : Nat)
    (hbase : base.size ≤ Padding.messageOffset) :
    MachineState.readWord (Padding.paddedMemory base input)
        (Padding.messageOffset + off) =
      MachineState.readWord (Padding.paddedMessage input) off := by
  unfold MachineState.readWord
  rw [readPadded_paddedMemory_shift base input off 32 hbase]

theorem shiftRight_readWord_paddedMemory_224 (base input : ByteArray)
    (off : Nat) (hbase : base.size ≤ Padding.messageOffset) :
    UInt256.shiftRight
        (MachineState.readWord (Padding.paddedMemory base input)
          (Padding.messageOffset + off))
        (UInt256.ofNat 224) =
      Challenge.EvmProof.Word.ofUInt32
        (Sha256.readBE32 (Padding.paddedMessage input) off) := by
  rw [readWord_paddedMemory_shift base input off hbase]
  exact shiftRight_readWord_224 (Padding.paddedMessage input) off

private theorem loadOffset_eq (input : ByteArray) (blockOff k : Nat)
    (hfit : Challenge.Sha256.CalldataFits input)
    (hblock : blockOff + 64 ≤ Padding.paddedLength input.size)
    (hk : k < 16) :
    Schedule.loadOffset
        (UInt256.ofNat (Padding.messageOffset + blockOff)) k =
      Padding.messageOffset + (blockOff + k * 4) := by
  have hpadded := Padding.paddedLength_lt input.size
  have hinput : input.size < 2 ^ 64 := hfit
  have haddr : Padding.messageOffset + blockOff + k * 4 < 2 ^ 256 := by
    have hsmall : Padding.messageOffset + blockOff + k * 4 <
        2 ^ 64 + 4096 := by
      simp only [Padding.messageOffset]
      omega
    exact lt_trans hsmall (by norm_num)
  unfold Schedule.loadOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by omega),
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
  · omega
  · omega

/-- The concrete padded memory and block pointer establish the exact
four-byte-reader seam expected by the generic schedule proof. -/
theorem paddedBlockAt (s : State) (base input : ByteArray)
    (msgOff : UInt256) (blockOff : Nat)
    (hmemory : s.memory = Padding.paddedMemory base input)
    (hbase : base.size ≤ Padding.messageOffset)
    (hmsgOff : msgOff = UInt256.ofNat (Padding.messageOffset + blockOff))
    (hfit : Challenge.Sha256.CalldataFits input)
    (hblock : blockOff + 64 ≤ Padding.paddedLength input.size) :
    ScheduleCorrect.PaddedBlockAt s.memory msgOff
      (Padding.paddedMessage input) blockOff := by
  intro k hk
  rw [hmemory, hmsgOff]
  unfold Schedule.initialWord
  rw [loadOffset_eq input blockOff k hfit hblock hk]
  exact shiftRight_readWord_paddedMemory_224 base input (blockOff + k * 4)
    hbase

/-- The same concrete pointer also puts every message read above all schedule
scratch slots. -/
theorem scheduleSeparated (input : ByteArray) (msgOff : UInt256)
    (blockOff : Nat)
    (hmsgOff : msgOff = UInt256.ofNat (Padding.messageOffset + blockOff))
    (hfit : Challenge.Sha256.CalldataFits input)
    (hblock : blockOff + 64 ≤ Padding.paddedLength input.size) :
    ∀ k, k < 16 →
      Padding.messageOffset ≤ Schedule.loadOffset msgOff k := by
  intro k hk
  rw [hmsgOff, loadOffset_eq input blockOff k hfit hblock hk]
  omega

/-- Both caller-side hypotheses of
`ScheduleCorrect.scheduleResult_slots_of_paddedBlockAt`, packaged for direct
use by the reference execution proof. -/
theorem paddedBlockAt_and_separated (s : State) (base input : ByteArray)
    (msgOff : UInt256) (blockOff : Nat)
    (hmemory : s.memory = Padding.paddedMemory base input)
    (hbase : base.size ≤ Padding.messageOffset)
    (hmsgOff : msgOff = UInt256.ofNat (Padding.messageOffset + blockOff))
    (hfit : Challenge.Sha256.CalldataFits input)
    (hblock : blockOff + 64 ≤ Padding.paddedLength input.size) :
    ScheduleCorrect.PaddedBlockAt s.memory msgOff
        (Padding.paddedMessage input) blockOff ∧
      (∀ k, k < 16 →
        Padding.messageOffset ≤ Schedule.loadOffset msgOff k) := by
  exact ⟨paddedBlockAt s base input msgOff blockOff hmemory hbase hmsgOff
      hfit hblock,
    scheduleSeparated input msgOff blockOff hmsgOff hfit hblock⟩

end Challenge.Sha256.Reference.Proofs.Bytecode.PaddedBlockBridge
