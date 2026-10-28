import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleCorrect
import YulEvmCompiler.BytesLemmas

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Padded-memory bridge for the RIPEMD-160 schedule

This file connects the bytecode's `MLOAD`/`BYTE` little-endian reader to the
pinned `Crypto.Ripemd160.readLE32` reader over every complete 64-byte block of
the one-pass padded image.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.WordReader

open EvmSemantics
open EvmSemantics.Crypto
open EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding

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

/-- `BYTE 0..3` after MLOAD returns the corresponding zero-padded memory
byte. -/
theorem byteAt_readWord (bs : ByteArray) (off i : Nat) (hi : i < 4) :
    UInt256.byteAt (UInt256.ofNat i) (MachineState.readWord bs off) =
      UInt256.ofNat (bs[off + i]?.getD 0).toNat := by
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
  have hfirstBytes := bytesToBigEndianNat_readPadded_four bs off
  change first =
    ((((bs[off]?.getD 0).toNat * 256 +
        (bs[off + 1]?.getD 0).toNat) * 256 +
        (bs[off + 2]?.getD 0).toNat) * 256) +
      (bs[off + 3]?.getD 0).toNat at hfirstBytes
  have hb0 := (bs[off]?.getD 0).toNat_lt
  have hb1 := (bs[off + 1]?.getD 0).toNat_lt
  have hb2 := (bs[off + 2]?.getD 0).toNat_lt
  have hb3 := (bs[off + 3]?.getD 0).toNat_lt
  unfold MachineState.readWord UInt256.byteAt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 256), if_neg (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hvalue, hsplit]
  change UInt256.ofNat
      (((first * 256 ^ 28 + rest) >>> (8 * (31 - i))) &&& 0xff) = _
  rw [show (0xff : Nat) = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [hfirstBytes]
  interval_cases i
  · let tail := (((bs[off + 1]?.getD 0).toNat * 256 +
      (bs[off + 2]?.getD 0).toNat) * 256 +
      (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest
    have htail : tail < 256 ^ 31 := by
      dsimp [tail]
      norm_num [pow_mul] at *
      omega
    have hrearrange :
        (((((bs[off]?.getD 0).toNat * 256 +
              (bs[off + 1]?.getD 0).toNat) * 256 +
              (bs[off + 2]?.getD 0).toNat) * 256 +
              (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest) =
          (bs[off]?.getD 0).toNat * 256 ^ 31 + tail := by
      dsimp [tail]
      ring
    have hden : 2 ^ (8 * (31 - 0)) = 256 ^ 31 := by norm_num [pow_mul]
    rw [hden, hrearrange,
      Nat.mul_comm (bs[off]?.getD 0).toNat (256 ^ 31),
      Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt htail, Nat.add_zero,
      Nat.mod_eq_of_lt hb0]
    simp
  · let pre := (bs[off]?.getD 0).toNat * 256 +
      (bs[off + 1]?.getD 0).toNat
    let tail := ((bs[off + 2]?.getD 0).toNat * 256 +
      (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest
    have htail : tail < 256 ^ 30 := by
      dsimp [tail]
      norm_num [pow_mul] at *
      omega
    have hrearrange :
        (((((bs[off]?.getD 0).toNat * 256 +
              (bs[off + 1]?.getD 0).toNat) * 256 +
              (bs[off + 2]?.getD 0).toNat) * 256 +
              (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest) =
          pre * 256 ^ 30 + tail := by
      dsimp [pre, tail]
      ring
    have hden : 2 ^ (8 * (31 - 1)) = 256 ^ 30 := by norm_num [pow_mul]
    rw [hden, hrearrange, Nat.mul_comm pre (256 ^ 30),
      Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt htail, Nat.add_zero]
    dsimp [pre]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hb1]
  · let pre := ((bs[off]?.getD 0).toNat * 256 +
      (bs[off + 1]?.getD 0).toNat) * 256 +
      (bs[off + 2]?.getD 0).toNat
    let tail := (bs[off + 3]?.getD 0).toNat * 256 ^ 28 + rest
    have htail : tail < 256 ^ 29 := by
      dsimp [tail]
      norm_num [pow_mul] at *
      omega
    have hrearrange :
        (((((bs[off]?.getD 0).toNat * 256 +
              (bs[off + 1]?.getD 0).toNat) * 256 +
              (bs[off + 2]?.getD 0).toNat) * 256 +
              (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest) =
          pre * 256 ^ 29 + tail := by
      dsimp [pre, tail]
      ring
    have hden : 2 ^ (8 * (31 - 2)) = 256 ^ 29 := by norm_num [pow_mul]
    rw [hden, hrearrange, Nat.mul_comm pre (256 ^ 29),
      Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt htail, Nat.add_zero]
    dsimp [pre]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hb2]
  · let pre := (((bs[off]?.getD 0).toNat * 256 +
      (bs[off + 1]?.getD 0).toNat) * 256 +
      (bs[off + 2]?.getD 0).toNat) * 256 +
      (bs[off + 3]?.getD 0).toNat
    have hrearrange :
        (((((bs[off]?.getD 0).toNat * 256 +
              (bs[off + 1]?.getD 0).toNat) * 256 +
              (bs[off + 2]?.getD 0).toNat) * 256 +
              (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest) =
          pre * 256 ^ 28 + rest := by rfl
    have hden : 2 ^ (8 * (31 - 3)) = 256 ^ 28 := by norm_num [pow_mul]
    rw [hden, hrearrange, Nat.mul_comm pre (256 ^ 28),
      Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt hrest, Nat.add_zero]
    dsimp [pre]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hb3]

private theorem readLE32_eq_bytes (bs : ByteArray) (off : Nat) :
    Crypto.Ripemd160.readLE32 bs off =
      let b0 := (bs[off]?.getD 0).toUInt32
      let b1 := (bs[off + 1]?.getD 0).toUInt32
      let b2 := (bs[off + 2]?.getD 0).toUInt32
      let b3 := (bs[off + 3]?.getD 0).toUInt32
      (b0 ||| (b1 <<< UInt32.ofNat 8)) |||
        ((b2 <<< UInt32.ofNat 16) ||| (b3 <<< UInt32.ofNat 24)) := by
  unfold Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [List.range', List.foldl_cons, List.foldl_nil]
  have hbyte (i : Nat) :
      (if h : off + i < bs.size then bs[off + i].toUInt32 else 0) =
        (bs[off + i]?.getD 0).toUInt32 := by
    by_cases h : off + i < bs.size <;> simp [h]
  rw [hbyte 0, hbyte 1, hbyte 2, hbyte 3]
  norm_num
  rw [UInt32.or_assoc]
  rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.shiftLeft_zero]

@[simp] private theorem ofNat_byte_eq_ofUInt32 (b : UInt8) :
    UInt256.ofNat b.toNat = Challenge.EvmProof.Word.ofUInt32 b.toUInt32 := by
  unfold Challenge.EvmProof.Word.ofUInt32
  rw [UInt8.toNat_toUInt32]

/-- The masked EVM `MLOAD`/`BYTE` little-endian reader is exactly the
mathematical RIPEMD-160 four-byte reader. -/
theorem mask32_readLEWord_eq_readLE32 (bs : ByteArray) (off : Nat)
    (hoff : off < 2 ^ 256) :
    Challenge.EvmProof.Word.mask32
        (Schedule.readLEWord bs (UInt256.ofNat off)) =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.readLE32 bs off) := by
  unfold Schedule.readLEWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  dsimp only
  rw [show ({ val := 0 } : UInt256) = UInt256.ofNat 0 by rfl]
  rw [byteAt_readWord bs off 0 (by omega),
    byteAt_readWord bs off 1 (by omega),
    byteAt_readWord bs off 2 (by omega),
    byteAt_readWord bs off 3 (by omega)]
  simp only [Nat.add_zero, ofNat_byte_eq_ofUInt32]
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32]
  apply congrArg Challenge.EvmProof.Word.ofUInt32
  change Challenge.EvmProof.Word.toUInt32
      ((Challenge.EvmProof.Word.ofUInt32 (bs[off]?.getD 0).toUInt32 |||
          UInt256.shiftLeft
            (Challenge.EvmProof.Word.ofUInt32 (bs[off + 1]?.getD 0).toUInt32)
            (UInt256.ofNat 8)) |||
        (UInt256.shiftLeft
            (Challenge.EvmProof.Word.ofUInt32 (bs[off + 2]?.getD 0).toUInt32)
            (UInt256.ofNat 16) |||
          UInt256.shiftLeft
            (Challenge.EvmProof.Word.ofUInt32 (bs[off + 3]?.getD 0).toUInt32)
            (UInt256.ofNat 24))) = _
  rw [Challenge.EvmProof.Word.toUInt32_or,
    Challenge.EvmProof.Word.toUInt32_or,
    Challenge.EvmProof.Word.toUInt32_or,
    Challenge.EvmProof.Word.toUInt32_ofUInt32]
  rw [Challenge.EvmProof.Word.toUInt32_shiftLeft_ofUInt32 _ 8 (by omega),
    Challenge.EvmProof.Word.toUInt32_shiftLeft_ofUInt32 _ 16 (by omega),
    Challenge.EvmProof.Word.toUInt32_shiftLeft_ofUInt32 _ 24 (by omega),
    readLE32_eq_bytes]


#print axioms mask32_readLEWord_eq_readLE32
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.WordReader
