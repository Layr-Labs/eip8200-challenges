import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144LegacyProduct
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound
set_option warningAsError true
set_option maxRecDepth 10000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarWide
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144Nat
open Paired144LegacyProduct Paired144WordRound

private theorem product_window (a b n : Nat) (hn0 : 6 ≤ n) (hn : n ≤ 40) :
    (((a + b * 2^144) * ((2^32+1)*(2^6+2^72))) % 2^256) / 2^n % 2^32 =
      a * (2^32+1) / 2^(n-6) % 2^32 := by
  rw [truncate_window _ n 32 256 (by omega)]
  have hd : (a + b * 2^144) * ((2^32+1)*(2^6+2^72)) =
      a * ((2^32+1)*(2^6+2^72)) + (b * ((2^32+1)*(2^6+2^72))) * 2^144 := by
    rw [Nat.add_mul]
    ac_rfl
  rw [hd, div_pow_add_mul_pow _ _ n 144 (by omega),
    mod_pow_add_mul_pow _ _ (144-n) 32 (by omega),
    ← Nat.mul_assoc, Nat.mul_add,
    div_pow_add_mul_pow _ _ n 72 (by omega),
    mod_pow_add_mul_pow _ _ (72-n) 32 (by omega),
    mul_pow_div_pow _ 6 n hn0]

private theorem coefficient_nat : coefficient.toNat = (2^32+1)*(2^6+2^72) := by decide

private theorem low_shift_nat (x : BitVec 256) (n : Nat) :
    (low (x >>> n)).toNat = x.toNat / 2^n % 2^32 := by
  simp only [low, BitVec.extractLsb'_toNat, Nat.pow_zero, Nat.div_one,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem product_nat (a b : BitVec 32) :
    (pack a b * coefficient).toNat =
      ((a.toNat+b.toNat*2^144)*((2^32+1)*(2^6+2^72)))%2^256 :=
  (BitVec.toNat_mul (pack a b) coefficient).trans
    (congrArg₂ (fun x y : Nat => x*y%2^256) (pack_toNat a b) coefficient_nat)

private theorem low_product_nat (a b : BitVec 32) (n : Nat) :
    (low ((pack a b * coefficient) >>> n)).toNat =
      (((a.toNat+b.toNat*2^144)*((2^32+1)*(2^6+2^72)))%2^256)/2^n%2^32 :=
  (low_shift_nat (pack a b * coefficient) n).trans
    (congrArg (fun x : Nat => x/2^n%2^32) (product_nat a b))

theorem low_rotate (a b : BitVec 32) (r : Nat) (hr0 : 0 < r) (hr : r < 32) :
    low ((pack a b * coefficient) >>> (38-r)) = a.rotateLeft r := by
  apply BitVec.eq_of_toNat_eq
  rw [low_product_nat, product_window _ _ (38-r) (by omega) (by omega),
    show 38-r-6 = 32-r by omega]
  exact (rotate_toNat a r hr0 hr).symm

theorem bits_wordShift (x : UInt256) (n : Nat) (hn : n < 256) :
    bits (wordShift x n) = (bits x * coefficient) >>> n := by
  rw [wordShift, bits_shr _ n hn, bits_mul]
  rfl

#print axioms low_rotate
#print axioms bits_wordShift
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarWide
