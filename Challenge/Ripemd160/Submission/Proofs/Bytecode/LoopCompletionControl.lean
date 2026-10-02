import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverModel
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- The absolute loop limit.  Fast-entry inputs (64, 128 or 192 bytes) store the end of their
data, `1056 + size`: the advanced offset meets it exactly and then takes the dedicated padding
block.  Every other input, including whole-block inputs of 256 bytes or more, stores
`959 + paddedLength`: the unadvanced offset of the last block, `992 + paddedLength`, is the
first one past it, and no advanced offset (all `≡ 32 mod 64`) ever equals it. -/
def limitNat (input : ByteArray) : Nat :=
  if input.size % 64 = 0 ∧ input.size < 256 then 1056 + input.size
  else 959 + Padding.paddedLength input.size

/-- The raw limit slot: block pointers are absolute memory addresses `1056 + 64 i`. -/
def limit (input : ByteArray) : UInt256 := UInt256.ofNat (limitNat input)

def blockPC (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.ofNat (if input.size = i * 64 ∧ input.size < 256 then 129 else 458)

theorem limitNat_lt (input : ByteArray) (hsize : input.size < 2^64) :
    limitNat input < 2^64 + 2000 := by
  have hb := Padding.paddedLength_lt input.size
  unfold limitNat
  split <;> omega

theorem limit_toNat (input : ByteArray) (hsize : input.size < 2^64) :
    (limit input).toNat = limitNat input := by
  have hl := limitNat_lt input hsize
  have h2 : (2:Nat)^64 + 2000 < 2^256 := by decide
  change limitNat input % 2^256 = limitNat input
  exact Nat.mod_eq_of_lt (by omega)

/-- The pad-only block is always the last block. -/
theorem pad_last (input : ByteArray) (i : Nat)
    (hh : input.size = i * 64 ∧ input.size < 256) : i + 1 = DriverTrace.blockCount input := by
  unfold DriverTrace.blockCount Padding.paddedLength
  omega

/-- Before the last block the unadvanced offset never passes the limit. -/
theorem not_finish (input : ByteArray) (i : Nat)
    (hi : i + 1 < DriverTrace.blockCount input) : 1056 + i * 64 ≤ limitNat input := by
  unfold DriverTrace.blockCount Padding.paddedLength at hi
  unfold limitNat Padding.paddedLength
  split <;> omega

theorem pad_hit (input : ByteArray) (i : Nat)
    (hh : input.size = (i + 1) * 64 ∧ input.size < 256) : 1056 + (i + 1) * 64 = limitNat input := by
  unfold limitNat
  rw [if_pos (by omega)]
  omega

theorem pad_miss (input : ByteArray) (i : Nat)
    (hh : ¬ (input.size = (i + 1) * 64 ∧ input.size < 256)) : 1056 + (i + 1) * 64 ≠ limitNat input := by
  unfold limitNat Padding.paddedLength
  split <;> omega

/-- A last block that is not the pad-only block (the cold route) finishes on its own offset. -/
theorem finish_cold (input : ByteArray)
    (hh : ¬ (input.size = (DriverTrace.blockCount input - 1) * 64 ∧ input.size < 256)) :
    limitNat input < 1056 + (DriverTrace.blockCount input - 1) * 64 := by
  unfold DriverTrace.blockCount Padding.paddedLength at hh
  unfold DriverTrace.blockCount limitNat Padding.paddedLength
  split <;> omega

theorem limit_aligned (input : ByteArray) (hz : input.size % 64 = 0 ∧ input.size < 256) :
    limit input = UInt256.ofNat (1056 + input.size) := by
  simp only [limit, limitNat, if_pos hz]

theorem limit_cold (input : ByteArray) (hz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) :
    limit input = UInt256.ofNat (959 + Padding.paddedLength input.size) := by
  simp only [limit, limitNat, if_neg hz]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
