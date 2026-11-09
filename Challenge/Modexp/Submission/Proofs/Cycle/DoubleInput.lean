import Challenge.EvmProof.Word
import Mathlib.Data.Nat.ModEq

set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
Shared input doubling for a square's low/high product pair. This is an
arithmetic building block, not yet wired into the executable square proof.
The residue sums need not be equal as words; only the final MULMOD is equal.
-/
namespace CycleSubmission.DoubleInput
open EvmSemantics Challenge.EvmProof.Word

theorem mulMod_nat (a b p : UInt256) (hp : 0 < p.toNat) :
    (UInt256.mulMod a b p).toNat = (a.toNat * b.toNat) % p.toNat := by
  have hn : p.val.val ≠ 0 := by change p.toNat ≠ 0; omega
  unfold UInt256.mulMod
  rw [if_neg hn, word_toNat_ofNat]
  exact Nat.mod_eq_of_lt ((Nat.mod_lt _ hp).trans p.val.isLt)

private theorem mul_nat (a b : UInt256) :
    (a*b).toNat = (a.toNat*b.toNat) % 2^256 := by
  change (a.val*b.val).val = _
  rw [Fin.val_mul]
  rfl

/-- The wrapped low product permits factoring without any digit bound. -/
theorem low_double (a b : UInt256) : b*(a+a) = b*a+b*a := by
  apply word_ext
  rw [mul_nat, word_toNat_add, word_toNat_add, mul_nat]
  calc
    _ = (b.toNat * (a.toNat+a.toNat)) % 2^256 := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    _ = (b.toNat*a.toNat + b.toNat*a.toNat) % 2^256 := by rw [Nat.mul_add]
    _ = _ := Nat.add_mod _ _ _

/-- A doubled input can replace two copies of the residue product once the
existing column reduction is reached. The hypotheses prevent word wrapping
before reduction modulo p; the low product above does not need them. -/
theorem high_double (a b p h factor : UInt256)
    (hp : 0 < p.toNat)
    (ha : a.toNat+a.toNat < 2^256)
    (hroom : 2*p.toNat+h.toNat ≤ 2^256) :
    UInt256.mulMod factor (UInt256.mulMod b (a+a) p + h) p =
      UInt256.mulMod factor
        (UInt256.mulMod b a p + UInt256.mulMod b a p + h) p := by
  have hdouble : (a+a).toNat = a.toNat+a.toNat := by
    rw [word_toNat_add, Nat.mod_eq_of_lt ha]
  have hprod := Nat.mod_lt (b.toNat*a.toNat) hp
  have hnew := Nat.mod_lt (b.toNat*(a.toNat+a.toNat)) hp
  have hsmall : (b.toNat*a.toNat)%p.toNat + (b.toNat*a.toNat)%p.toNat < 2^256 := by omega
  have hold : (b.toNat*a.toNat)%p.toNat + (b.toNat*a.toNat)%p.toNat + h.toNat < 2^256 := by omega
  have hnewsum : (b.toNat*(a.toNat+a.toNat))%p.toNat + h.toNat < 2^256 := by omega
  apply word_ext
  simp only [mulMod_nat _ _ _ hp, word_toNat_add, hdouble]
  rw [Nat.mod_eq_of_lt hnewsum, Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hold]
  have hcong :
      ((b.toNat*(a.toNat+a.toNat))%p.toNat + h.toNat) % p.toNat =
        ((b.toNat*a.toNat)%p.toNat + (b.toNat*a.toNat)%p.toNat + h.toNat) % p.toNat := by
    simp only [Nat.mul_add, Nat.add_mod, Nat.mod_mod]
  calc
    _ = ((factor.toNat % p.toNat) *
      (((b.toNat*(a.toNat+a.toNat))%p.toNat + h.toNat) % p.toNat)) % p.toNat := Nat.mul_mod _ _ _
    _ = ((factor.toNat % p.toNat) *
      (((b.toNat*a.toNat)%p.toNat + (b.toNat*a.toNat)%p.toNat + h.toNat) % p.toNat)) % p.toNat := by rw [hcong]
    _ = _ := (Nat.mul_mod _ _ _).symm

theorem addA (a b c : UInt256) : (a+b)+c = a+(b+c) := by
  apply word_ext
  simp only [word_toNat_add]
  have ha := a.val.isLt
  have hc := c.val.isLt
  change a.toNat < 2^256 at ha
  change c.toNat < 2^256 at hc
  conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [Nat.add_assoc]
theorem addL (a b c : UInt256) : a+(b+c) = b+(a+c) := by
  rw [← addA, word_add_comm a b, addA]

/-- The complete column residue sum, including carry and two quotient products. -/
theorem high_double_column (a b p c r t factor : UInt256)
    (hp : 0 < p.toNat) (ha : a.toNat+a.toNat < 2^256)
    (hc : c.toNat < p.toNat) (hr : r.toNat < p.toNat) (ht : t.toNat < p.toNat)
    (hroom : 5*p.toNat ≤ 2^256) :
    UInt256.mulMod factor (t + (r + (c + UInt256.mulMod b (a+a) p))) p =
      UInt256.mulMod factor (t + (r + (c + (UInt256.mulMod b a p + UInt256.mulMod b a p)))) p := by
  have hct : (r+c).toNat = r.toNat+c.toNat := by
    rw [word_toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hsum : (t+(r+c)).toNat = t.toNat+r.toNat+c.toNat := by
    rw [word_toNat_add, hct, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
  have hbound : 2*p.toNat+(t+(r+c)).toNat ≤ 2^256 := by rw [hsum]; omega
  have hh := high_double a b p (t+(r+c)) factor hp ha hbound
  simpa only [addA, word_add_comm, addL] using hh

/-- Specialize the column rewrite to the radix-240 kernel. All three incoming
residues, including the carry, are already MULMOD outputs. Thus the only
caller-supplied arithmetic invariant is the real input digit bound. This
does not assert that the unbounded square execution API has that invariant. -/
theorem high_double_radix240
    (a b carryFactor carrySum r0 r1 t0 t1 factor : UInt256)
    (ha : a.toNat < 2^240) :
    let p := UInt256.ofNat (2^251-1)
    let c := UInt256.mulMod carryFactor carrySum p
    let r := UInt256.mulMod r0 r1 p
    let t := UInt256.mulMod t0 t1 p
    UInt256.mulMod factor (t + (r + (c + UInt256.mulMod b (a+a) p))) p =
      UInt256.mulMod factor
        (t + (r + (c + (UInt256.mulMod b a p + UInt256.mulMod b a p)))) p := by
  dsimp only
  let p := UInt256.ofNat (2^251-1)
  have hpval : p.toNat = 2^251-1 := by
    change (UInt256.ofNat (2^251-1)).toNat = _
    rw [word_toNat_ofNat]
    norm_num
  have hp : 0 < p.toNat := by rw [hpval]; norm_num
  have hroom : 5*p.toNat ≤ 2^256 := by rw [hpval]; norm_num
  have hdouble : a.toNat+a.toNat < 2^256 := by omega
  have residue_lt (x y : UInt256) : (UInt256.mulMod x y p).toNat < p.toNat := by
    rw [mulMod_nat _ _ _ hp]
    exact Nat.mod_lt _ hp
  exact high_double_column a b p
    (UInt256.mulMod carryFactor carrySum p)
    (UInt256.mulMod r0 r1 p) (UInt256.mulMod t0 t1 p) factor
    hp hdouble (residue_lt _ _) (residue_lt _ _) (residue_lt _ _) hroom

#print axioms high_double_radix240
#print axioms low_double
#print axioms high_double
#print axioms high_double_column
end CycleSubmission.DoubleInput
