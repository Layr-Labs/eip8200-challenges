import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleCorrect

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedDriverBounds

open EvmSemantics Challenge.EvmProof

def source (i : Nat) : Nat := Padding.messageOffset + DriverTrace.blockOffset i

theorem source_ge_512 (i : Nat) : 512 ≤ source i := by
  simp only [source, Padding.messageOffset]
  omega

/-- The entire two-word preprocessing read lies below the UInt256 wrap point. -/
theorem source_window_lt (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < DriverTrace.blockCount input) : source i + 64 < 2 ^ 256 := by
  have hpad := Padding.paddedLength_lt input.size
  have hoff : DriverTrace.blockOffset i + 64 ≤ Padding.paddedLength input.size := by
    rw [DriverTrace.paddedLength_eq_blockCount input]
    unfold DriverTrace.blockOffset
    omega
  unfold Challenge.Ripemd160.CalldataFits at hfit
  norm_num [source, Padding.messageOffset] at hfit ⊢
  omega

theorem messageOffset_toNat (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < DriverTrace.blockCount input) :
    (DriverTrace.messageOffsetWord i).toNat = source i := by
  have hbound := source_window_lt input hfit i hi
  change (UInt256.ofNat (source i)).toNat = source i
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

#print axioms source_window_lt
#print axioms messageOffset_toNat

/-- The exact caller's block predicate supplies the unmasked mathematical
word values required by the packed endpoint theorem. -/
theorem expectedWord_toNat (memory padded : ByteArray) (msgOff : UInt256)
    (blockOff k : Nat) (hk : k < 16)
    (hblock : ScheduleCorrect.MessageBlockAt memory msgOff padded blockOff) :
    (ScheduleCorrect.expectedWord memory msgOff k).toNat =
      (Crypto.Ripemd160.readLE32 padded (blockOff + k * 4)).toNat := by
  rw [hblock k hk, Word.ofUInt32_toNat]

#print axioms expectedWord_toNat

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedDriverBounds
