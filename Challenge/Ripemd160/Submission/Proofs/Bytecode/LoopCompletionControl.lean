import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverModel
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def limitNat (input : ByteArray) : Nat :=
  if input.size % 64 = 0 then input.size else Padding.paddedLength input.size

def limit (input : ByteArray) : UInt256 := UInt256.ofNat (limitNat input)

def blockPC (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.ofNat (if input.size = i * 64 then 306 else 774)

theorem limit_le_padded (input : ByteArray) : limitNat input ≤ Padding.paddedLength input.size := by
  unfold limitNat Padding.paddedLength
  split <;> omega

theorem padded_bound (input : ByteArray) (hsize : input.size < 2^64) :
    DriverTrace.blockCount input * 64 < 2^256 := by
  rw [← DriverTrace.paddedLength_eq_blockCount]
  have h := Padding.paddedLength_lt input.size
  have hb : 2^64 + 73 < (2:Nat)^256 := by decide
  omega

theorem limit_toNat (input : ByteArray) (hsize : input.size < 2^64) :
    (limit input).toNat = limitNat input := by
  have hb := padded_bound input hsize
  have hl := limit_le_padded input
  rw [DriverTrace.paddedLength_eq_blockCount] at hl
  change limitNat input % 2^256 = limitNat input
  exact Nat.mod_eq_of_lt (by omega)

theorem continue_lt (input : ByteArray) (i : Nat)
    (hi : i + 1 < DriverTrace.blockCount input)
    (hne : input.size ≠ (i + 1) * 64) :
    (i + 1) * 64 < limitNat input := by
  unfold limitNat
  unfold DriverTrace.blockCount Padding.paddedLength at hi
  split
  · omega
  · unfold Padding.paddedLength
    omega

theorem pad_bound (input : ByteArray) (i : Nat)
    (heq : input.size = (i + 1) * 64) : limitNat input ≤ (i + 1) * 64 := by
  have hz : input.size % 64 = 0 := by omega
  simp only [limitNat, if_pos hz]
  omega

theorem finish_bound (input : ByteArray) : limitNat input ≤ DriverTrace.blockCount input * 64 := by
  rw [← DriverTrace.paddedLength_eq_blockCount]
  exact limit_le_padded input

theorem finish_miss (input : ByteArray) : input.size ≠ DriverTrace.blockCount input * 64 := by
  rw [← DriverTrace.paddedLength_eq_blockCount]
  unfold Padding.paddedLength
  omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
