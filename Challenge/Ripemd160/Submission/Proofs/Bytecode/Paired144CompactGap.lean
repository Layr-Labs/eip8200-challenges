import Init.Data.BitVec.Lemmas

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactGap

def coefficient (u v : Nat) : BitVec 256 :=
  BitVec.ofNat 256 ((2 ^ 32 + 1) * (2 ^ u + 2 ^ (72 + v)))

def rawProduct (a b : BitVec 32) (u v : Nat) : BitVec 256 :=
  (BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< (72 : Nat))) *
    coefficient u v

private theorem low_term_lt (a : BitVec 32) (u : Nat) (hu : u ≤ 7) :
    a.toNat * (2 ^ 32 + 1) * 2 ^ u < 2 ^ 71 := by
  have hp : 2 ^ u ≤ 128 := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hu
  have ha := a.isLt
  calc
    a.toNat * (2 ^ 32 + 1) * 2 ^ u ≤
        a.toNat * (2 ^ 32 + 1) * 128 := Nat.mul_le_mul_left _ hp
    _ < 2 ^ 71 := by
      simp only [Nat.reducePow] at *
      omega

/-- The low residue is exactly the low contribution. No bound on v,
nor a min(u,v)=0 premise, is needed for this local carry separator. -/
theorem rawProduct_low72_eq (a b : BitVec 32) (u v : Nat) (hu : u ≤ 7) :
    (rawProduct a b u v).toNat % 2 ^ 72 =
      a.toNat * (2 ^ 32 + 1) * 2 ^ u := by
  have hdiv : 2 ^ 72 ∣ 2 ^ 256 := Nat.pow_dvd_pow 2 (by decide)
  have hterm := low_term_lt a u hu
  have ha : a.toNat < 2 ^ 72 := by have h := a.isLt; omega
  have hv : 2 ^ (72 + v) % 2 ^ 72 = 0 := by
    simp only [Nat.pow_add, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  have hb : b.toNat * 2 ^ 72 % 2 ^ 72 = 0 := by
    simp only [Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
  have hc : (2 ^ 32 + 1) * (2 ^ u + 2 ^ (72 + v)) % 2 ^ 72 =
      ((2 ^ 32 + 1) * 2 ^ u) % 2 ^ 72 := by
    calc
      _ = ((2 ^ 32 + 1) % 2 ^ 72 *
          ((2 ^ u + 2 ^ (72 + v)) % 2 ^ 72)) % 2 ^ 72 := Nat.mul_mod _ _ _
      _ = ((2 ^ 32 + 1) % 2 ^ 72 * (2 ^ u % 2 ^ 72)) % 2 ^ 72 := by
        rw [Nat.add_mod (2 ^ u) (2 ^ (72 + v)) (2 ^ 72), hv]
        simp only [Nat.add_zero, Nat.mod_mod]
      _ = _ := (Nat.mul_mod _ _ _).symm
  simp only [rawProduct, coefficient, BitVec.toNat_mul, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]
  rw [Nat.mod_mod_of_dvd _ hdiv]
  have heq : ((a.toNat + b.toNat * 2 ^ 72) *
      ((2 ^ 32 + 1) * (2 ^ u + 2 ^ (72 + v)))) % 2 ^ 72 =
      a.toNat * (2 ^ 32 + 1) * 2 ^ u := by
    calc
      _ = (((a.toNat + b.toNat * 2 ^ 72) % 2 ^ 72) *
          (((2 ^ 32 + 1) * (2 ^ u + 2 ^ (72 + v))) % 2 ^ 72)) % 2 ^ 72 :=
        Nat.mul_mod _ _ _
      _ = (a.toNat * (((2 ^ 32 + 1) * 2 ^ u) % 2 ^ 72)) % 2 ^ 72 := by
        rw [hc]
        simp only [Nat.add_mod, hb, Nat.mod_eq_of_lt ha, Nat.add_zero]
      _ = (a.toNat * ((2 ^ 32 + 1) * 2 ^ u)) % 2 ^ 72 := Nat.mul_mod_mod _ _ _
      _ = _ := by
        rw [← Nat.mul_assoc]
        exact Nat.mod_eq_of_lt (by omega)
  exact heq

theorem rawProduct_low72_lt (a b : BitVec 32) (u v : Nat) (hu : u ≤ 7) :
    (rawProduct a b u v).toNat % 2 ^ 72 < 2 ^ 71 := by
  rw [rawProduct_low72_eq a b u v hu]
  exact low_term_lt a u hu

theorem rawProduct_gap71 (a b : BitVec 32) (u v : Nat) (hu : u ≤ 7) :
    (rawProduct a b u v).getLsbD 71 = false := by
  have hlow := rawProduct_low72_lt a b u v hu
  rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_false_iff_not.mpr
  simp only [Nat.reducePow] at *
  omega

theorem shiftedProduct_gap (a b : BitVec 32) (u v n : Nat)
    (hu : u ≤ 7) (hn : n ≤ 71) :
    (rawProduct a b u v >>> n).getLsbD (71 - n) = false := by
  rw [BitVec.getLsbD_ushiftRight]
  have hindex : n + (71 - n) = 71 := by omega
  rw [hindex]
  exact rawProduct_gap71 a b u v hu

#print axioms rawProduct_low72_eq
#print axioms rawProduct_low72_lt
#print axioms rawProduct_gap71
#print axioms shiftedProduct_gap

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactGap
