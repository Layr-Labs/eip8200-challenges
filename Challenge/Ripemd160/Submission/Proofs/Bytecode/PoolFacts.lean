import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificatesV2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolFacts
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PoolShape PoolShapeV2

theorem window_zero (m : ByteArray) (a n : Nat)
    (hz : ∀ k, k < n → m[a+k]?.getD 0 = 0) :
    Precompile.bytesToNatPadded m a n = 0 := by
  induction n with
  | zero => exact Bytes.bytesToNatPadded_zero_width m a
  | succ n ih =>
    rw [Bytes.bytesToNatPadded_succ, ih (fun k hk => hz k (by omega)),
      PoolByte.byteFrom, hz n (by omega)]
    rfl

theorem zero_from_window (m : ByteArray) (a n k : Nat)
    (hz : Precompile.bytesToNatPadded m a n = 0) (hk : k < n) :
    m[a+k]?.getD 0 = 0 := by
  have h := Bytes.bytesToNatPadded_add m a (k+1) (n-(k+1))
  rw [show k+1+(n-(k+1))=n by omega, hz] at h
  have hp : 0 < 256^(n-(k+1)) := Nat.pow_pos (by decide)
  have hzero : Precompile.bytesToNatPadded m a (k+1) = 0 := by nlinarith
  rw [Bytes.bytesToNatPadded_succ, PoolByte.byteFrom] at hzero
  apply UInt8.toNat_inj.mp
  change _ = 0
  omega

theorem low_value (m : ByteArray) (a : Nat) :
    (MachineState.readWord m a).toNat % 2^32 =
      Precompile.bytesToNatPadded m (a+28) 4 := by
  simpa using StaggerTableMemory.readWord_mod_pow m a 4 (by decide)

theorem high_value (m : ByteArray) (a : Nat) :
    (MachineState.readWord m a).toNat / 2^144 % 2^32 =
      Precompile.bytesToNatPadded m (a+10) 4 := by
  have h := Bytes.readWord_shift_toNat m a 14 (by decide)
  rw [Nat.shiftRight_eq_div_pow] at h
  rw [show (32-14)*8=144 from rfl] at h
  rw [h, show (14:Nat)=10+4 from rfl, Bytes.bytesToNatPadded_add]
  have hb := Bytes.bytesToNatPadded_lt_pow m (a+10) 4
  norm_num only [Nat.reducePow] at hb ⊢
  omega

theorem zero_byte_slack (w : UInt256) (k : Nat) (hk : 14 ≤ k) (hk' : k ≤ 26)
    (hz : PoolByte.byte w k = 0) : w.toNat % 2^144 + 2^40 ≤ 2^144 := by
  have h := congrArg UInt8.toNat hz
  rw [PoolByte.byte_toNat] at h
  change w.toNat / 2^(8*(31-k)) % 256 = 0 at h
  interval_cases k <;> norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow] at h ⊢ <;> omega

theorem low_clear (m : ByteArray) (hz : ∀ k, 14 ≤ k → k < 28 → m[k]?.getD 0 = 0) :
    (MachineState.readWord m 0).toNat % 2^144 < 2^32 := by
  have h := StaggerTableMemory.readWord_mod_pow m 0 18 (by decide)
  change (MachineState.readWord m 0).toNat % 2^144 = Precompile.bytesToNatPadded m 14 18 at h
  rw [h, show (18:Nat)=14+4 from rfl, Bytes.bytesToNatPadded_add,
    window_zero m 14 14 (fun k hk => hz (14+k) (by omega) (by omega))]
  simpa using Bytes.bytesToNatPadded_lt_pow m 28 4

/-- The actual image over `m` against the clean reference over ANY base `r` the reference
model accepts: the certificates' lane terms are equal and read no memory. -/
theorem result_lanes (m r : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (hr : Clear r)
    (j : Nat) (hj : j < 61) :
    (MachineState.readWord (resultMemoryV2 m lo hi) (18*j)).toNat % 2^32 =
      (MachineState.readWord (resultMemory true r lo hi) (18*j)).toNat % 2^32 ∧
    (MachineState.readWord (resultMemoryV2 m lo hi) (18*j)).toNat / 2^144 % 2^32 =
      (MachineState.readWord (resultMemory true r lo hi) (18*j)).toNat / 2^144 % 2^32 := by
  constructor
  · rw [low_value, low_value]
    apply StaggerTableMemory.bytesToNatPadded_congrOffset
    intro k hk
    obtain ⟨-, h2, -, f2⟩ := PoolCertificatesV2.lane_sources ⟨j,hj⟩ ⟨k,hk⟩
    rw [resultV2_shape m lo hi hc, result_shape r lo hi hr, h2]
    exact eval_memFree _ _ _ _ _ f2
  · rw [high_value, high_value]
    apply StaggerTableMemory.bytesToNatPadded_congrOffset
    intro k hk
    obtain ⟨h1, -, f1, -⟩ := PoolCertificatesV2.lane_sources ⟨j,hj⟩ ⟨k,hk⟩
    rw [resultV2_shape m lo hi hc, result_shape r lo hi hr, h1]
    exact eval_memFree _ _ _ _ _ f1

theorem result_slack (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (j : Nat) (hj : j < 61) :
    (MachineState.readWord (resultMemoryV2 m lo hi) (18*j)).toNat % 2^144 + 2^40 ≤ 2^144 := by
  obtain ⟨hl,hu,hz⟩ := PoolCertificatesV2.slack_sources ⟨j,hj⟩
  apply zero_byte_slack _ _ hl hu
  rw [PoolByte.read _ _ _ (by omega), resultV2_shape m lo hi hc, hz]
  rfl

theorem result_clear (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) :
    ClearV2 (resultMemoryV2 m lo hi) := by
  intro a ha
  rw [resultV2_shape m lo hi hc, PoolCertificatesV2.clear_sources a ha]
  rfl

theorem result_terminal (m r : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (hr : Clear r) :
    MachineState.readWord (resultMemoryV2 m lo hi) 594 =
      MachineState.readWord (resultMemory true r lo hi) 594 := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro k hk
  obtain ⟨h, f⟩ := PoolCertificatesV2.terminal_sources ⟨k,hk⟩
  rw [resultV2_shape m lo hi hc, result_shape r lo hi hr, h]
  exact eval_memFree _ _ _ _ _ f

#print axioms result_lanes
#print axioms result_slack
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolFacts
