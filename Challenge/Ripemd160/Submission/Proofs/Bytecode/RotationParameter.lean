import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationMultiply
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.Ring

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationParameter

open EvmSemantics
open Challenge.EvmProof.Word

theorem nat_factor_shift_eq (u r : Nat)
    (_hu : u < 2 ^ 32) (_hr0 : 0 < r) (hr32 : r < 32) :
    (u * (2 ^ 32 + 1)) >>> (32 - r) =
      (u * ((2 ^ 32 + 1) <<< r)) >>> 32 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hpow : 2 ^ 32 = 2 ^ (32 - r) * 2 ^ r := by
    rw [← pow_add]
    congr 1
    omega
  calc
    u * (2 ^ 32 + 1) / 2 ^ (32 - r) =
        (u * (2 ^ 32 + 1)) * 2 ^ r /
          (2 ^ (32 - r) * 2 ^ r) := by
      symm
      exact Nat.mul_div_mul_right (m := 2 ^ r)
        (u * (2 ^ 32 + 1)) (2 ^ (32 - r)) (by positivity)
    _ = u * ((2 ^ 32 + 1) * 2 ^ r) / 2 ^ 32 := by
      rw [← hpow]
      simp only [mul_assoc]

theorem nat_factor_shift_products_lt (u r : Nat)
    (hu : u < 2 ^ 32) (hr0 : 0 < r) (hr32 : r < 32) :
    u * (2 ^ 32 + 1) < 2 ^ 256 ∧
      u * ((2 ^ 32 + 1) <<< r) < 2 ^ 256 := by
  have hfactor_pos : 0 < 2 ^ 32 + 1 := by positivity
  have hfactor_lt : 2 ^ 32 + 1 < 2 ^ 33 := by norm_num
  have hshift_le : 2 ^ r ≤ 2 ^ 32 := by
    exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  constructor
  · calc
      u * (2 ^ 32 + 1) < 2 ^ 32 * (2 ^ 32 + 1) :=
        Nat.mul_lt_mul_of_pos_right hu hfactor_pos
      _ < 2 ^ 256 := by norm_num [← Nat.pow_add]
  · rw [Nat.shiftLeft_eq]
    have hscaled : (2 ^ 32 + 1) * 2 ^ r < 2 ^ 33 * 2 ^ 32 := by
      calc
        (2 ^ 32 + 1) * 2 ^ r ≤ (2 ^ 32 + 1) * 2 ^ 32 :=
          Nat.mul_le_mul_left _ hshift_le
        _ < 2 ^ 33 * 2 ^ 32 :=
          Nat.mul_lt_mul_of_pos_right hfactor_lt (by positivity)
    calc
      u * ((2 ^ 32 + 1) * 2 ^ r) <
          2 ^ 32 * ((2 ^ 32 + 1) * 2 ^ r) :=
        Nat.mul_lt_mul_of_pos_right hu (by positivity)
      _ < 2 ^ 32 * (2 ^ 33 * 2 ^ 32) :=
        Nat.mul_lt_mul_of_pos_left hscaled (by positivity)
      _ < 2 ^ 256 := by norm_num [← Nat.pow_add]

private theorem mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

private theorem factor_shift_lt (r : Nat) (hr32 : r < 32) :
    (0x100000001 : Nat) * 2 ^ r < 2 ^ 256 := by
  have hshift : 2 ^ r ≤ 2 ^ 32 := by
    exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  calc
    (0x100000001 : Nat) * 2 ^ r ≤ 0x100000001 * 2 ^ 32 :=
      Nat.mul_le_mul_left _ hshift
    _ < 2 ^ 256 := by norm_num [← Nat.pow_add]

theorem uint256_factor_shift_mod_bounds (u : UInt256) (r : Nat)
    (hu : u.toNat < 2 ^ 32) (hr0 : 0 < r) (hr32 : r < 32) :
    u.toNat * (2 ^ 32 + 1) < 2 ^ 256 ∧
      u.toNat * ((2 ^ 32 + 1) <<< r) < 2 ^ 256 := by
  exact nat_factor_shift_products_lt u.toNat r hu hr0 hr32

theorem factor_shift_eq (u : UInt256) (r : Nat)
    (hu : u.toNat < 2 ^ 32) (hr0 : 0 < r) (hr32 : r < 32) :
    UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) u)
        (UInt256.ofNat (32 - r)) =
      UInt256.shiftRight
        (UInt256.mul u
          (UInt256.shiftLeft (UInt256.ofNat (0x100000001 : Nat))
            (UInt256.ofNat r)))
        (UInt256.ofNat 32) := by
  have hbounds := uint256_factor_shift_mod_bounds u r hu hr0 hr32
  have hfactorShift :
      UInt256.shiftLeft (UInt256.ofNat (0x100000001 : Nat))
          (UInt256.ofNat r) =
        UInt256.ofNat ((0x100000001 : Nat) * 2 ^ r) := by
    exact Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by omega)
      (factor_shift_lt r hr32)
  have hmulLeft :
      (UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) u).toNat =
        u.toNat * (2 ^ 32 + 1) := by
    calc
      (UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) u).toNat =
          ((0x100000001 : Nat) * u.toNat) % 2 ^ 256 := by
            rw [mul_toNat, word_toNat_ofNat]
            have hfactor : (0x100000001 : Nat) % 2 ^ 256 = 0x100000001 :=
              Nat.mod_eq_of_lt (by norm_num)
            simp only [hfactor]
      _ = (u.toNat * (2 ^ 32 + 1)) % 2 ^ 256 := by
            have hfactor : (0x100000001 : Nat) = 2 ^ 32 + 1 := by norm_num
            rw [hfactor, Nat.mul_comm]
      _ = u.toNat * (2 ^ 32 + 1) := Nat.mod_eq_of_lt hbounds.1
  have hmulRight :
      (UInt256.mul u
          (UInt256.shiftLeft (UInt256.ofNat (0x100000001 : Nat))
            (UInt256.ofNat r))).toNat =
        u.toNat * ((0x100000001 : Nat) * 2 ^ r) := by
    have hraw : u.toNat * ((0x100000001 : Nat) * 2 ^ r) < 2 ^ 256 := by
      simpa [Nat.shiftLeft_eq] using hbounds.2
    rw [hfactorShift, mul_toNat, word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (factor_shift_lt r hr32)]
    rw [Nat.mod_eq_of_lt hraw]
  have hleft :
      (UInt256.shiftRight
          (UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) u)
          (UInt256.ofNat (32 - r))).toNat =
        (u.toNat * (2 ^ 32 + 1)) >>> (32 - r) := by
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by omega), hmulLeft]
  have hright :
      (UInt256.shiftRight
          (UInt256.mul u
            (UInt256.shiftLeft (UInt256.ofNat (0x100000001 : Nat))
              (UInt256.ofNat r)))
          (UInt256.ofNat 32)).toNat =
        (u.toNat * ((0x100000001 : Nat) * 2 ^ r)) >>> 32 := by
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num), hmulRight]
  apply Challenge.EvmProof.Word.word_ext
  rw [hleft, hright]
  convert (nat_factor_shift_eq u.toNat r hu hr0 hr32) using 1;
    norm_num [Nat.shiftLeft_eq]

theorem rawRot_mul_shifted (u : UInt256) (r : Nat)
    (hu : u.toNat < 2 ^ 32) (hr0 : 0 < r) (hr32 : r < 32) :
    UInt256.shiftRight
        (UInt256.mul u
          (UInt256.shiftLeft (UInt256.ofNat (0x100000001 : Nat))
            (UInt256.ofNat r)))
        (UInt256.ofNat 32) =
      StackRound.stackRawRot u r := by
  calc
    UInt256.shiftRight
        (UInt256.mul u
          (UInt256.shiftLeft (UInt256.ofNat (0x100000001 : Nat))
            (UInt256.ofNat r)))
        (UInt256.ofNat 32) =
        UInt256.shiftRight
          (UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) u)
          (UInt256.ofNat (32 - r)) :=
      (factor_shift_eq u r hu hr0 hr32).symm
    _ = StackRound.stackRawRot u r :=
      RotationMultiply.rawRot_mul u r hu (by omega)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationParameter
