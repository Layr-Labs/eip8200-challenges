import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactGap

set_option warningAsError true
set_option maxHeartbeats 500000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactProduct
open Paired144CompactGap

private theorem term_lt (a : BitVec 32) (u : Nat) (hu : u ≤ 7) :
    a.toNat * (2 ^ 32 + 1) * 2 ^ u < 2 ^ 71 := by
  have hp : 2 ^ u ≤ 128 := Nat.pow_le_pow_right (by decide : 0 < 2) hu
  have ha := a.isLt
  calc
    a.toNat * (2 ^ 32 + 1) * 2 ^ u ≤
        a.toNat * (2 ^ 32 + 1) * 128 := Nat.mul_le_mul_left _ hp
    _ < 2 ^ 71 := by simp only [Nat.reducePow] at *; omega

private theorem rawProduct_nat (a b : BitVec 32) (u v : Nat) :
    (rawProduct a b u v).toNat =
      (a.toNat * (2 ^ 32 + 1) * 2 ^ u +
        (a.toNat * (2 ^ 32 + 1) * 2 ^ v + b.toNat * (2 ^ 32 + 1) * 2 ^ u) * 2 ^ 72 +
        b.toNat * (2 ^ 32 + 1) * 2 ^ v * 2 ^ 144) % 2 ^ 256 := by
  simp only [rawProduct, coefficient, BitVec.toNat_mul, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]
  congr 1
  rw [show (144 : Nat) = 72 + 72 from rfl]
  simp only [Nat.pow_add, Nat.mul_add, Nat.add_mul]
  ac_rfl

/-- The cross coefficient fits below the second radix boundary. Thus the whole
high144 quotient equals the right product; no hidden carry enters that lane. -/
theorem rawProduct_high144_eq (a b : BitVec 32) (u v : Nat)
    (hu : u ≤ 7) (hv : v ≤ 7) :
    (rawProduct a b u v).toNat / 2 ^ 144 =
      b.toNat * (2 ^ 32 + 1) * 2 ^ v := by
  have hal := term_lt a u hu
  have ham := term_lt a v hv
  have hbm := term_lt b u hu
  have hbh := term_lt b v hv
  rw [rawProduct_nat]
  simp only [Nat.reducePow] at *
  omega

#print axioms rawProduct_high144_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactProduct
