import Challenge.Modexp.Submission.Proofs.Fast.FullBaseLogic
import Challenge.Modexp.Submission.Proofs.Fast.SquareModel

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.LazyBounds

open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs

def redc (R m a b q : Nat) : Nat := (a * b + q * m) / R

theorem redc_lt_left_add {R m a b q : Nat} (hR : 0 < R) (hm : 0 < m)
    (hb : b < R) (hq : q < R) : redc R m a b q < a + m := by
  unfold redc
  apply (Nat.div_lt_iff_lt_mul hR).2
  have hp : a * b ≤ a * R := Nat.mul_le_mul_left a (Nat.le_of_lt hb)
  have hq' : q * m < R * m := Nat.mul_lt_mul_of_pos_right hq hm
  nlinarith

theorem redc_radix_bounds {R m a b q : Nat} (hm : 0 < m) (hmR : m < R)
    (ha : a < R) (hb : b < R) (hq : q < R) :
    redc R m a b q < R + m ∧ R + m < 2 * R := by
  have hu := redc_lt_left_add (Nat.lt_trans hm hmR) hm hb hq (a := a)
  constructor <;> omega

theorem coefficient_step_lt {β Q mu i : Nat} (hQ : Q < β ^ i) (hmu : mu < β) :
    Q + mu * β ^ i < β ^ (i + 1) := by
  have hp : (mu + 1) * β ^ i ≤ β * β ^ i := Nat.mul_le_mul_right _ (by omega)
  rw [pow_succ]
  nlinarith

theorem cios_step_lazy {m β a bpre bi t Q mu i : Nat} (hβ : 0 < β)
    (hbi : bi < β) (ht : t < a + m) (hmu : mu < β) (hQ : Q < β ^ i)
    (hinv : t * β ^ i = a * bpre + Q * m)
    (hdiv : β ∣ t + a * bi + mu * m) :
    (t + a * bi + mu * m) / β * β ^ (i + 1) =
        a * (bpre + bi * β ^ i) + (Q + mu * β ^ i) * m ∧
      (t + a * bi + mu * m) / β < a + m ∧
      Q + mu * β ^ i < β ^ (i + 1) := by
  refine ⟨?_, Model.cios_bound_tight hβ hbi ht hmu, coefficient_step_lt hQ hmu⟩
  have hexact := Nat.div_mul_cancel hdiv
  calc (t + a * bi + mu * m) / β * β ^ (i + 1)
      = (t + a * bi + mu * m) / β * β * β ^ i := by ring
    _ = (t + a * bi + mu * m) * β ^ i := by rw [hexact]
    _ = t * β ^ i + (a * bi + mu * m) * β ^ i := by ring
    _ = a * bpre + Q * m + (a * bi + mu * m) * β ^ i := by rw [hinv]
    _ = a * (bpre + bi * β ^ i) + (Q + mu * β ^ i) * m := by ring

theorem top_limb_le_one {R u high low : Nat}
    (hu : u < 2 * R) (heq : u = high * R + low) : high ≤ 1 := by
  by_contra h
  have hh : 2 ≤ high := by omega
  have hmul := Nat.mul_le_mul_right R hh
  omega

theorem current_sqRows_lazy (m0 : ByteArray) (p a mm : Nat) (hn32 : p + 2 ≤ 8)
    (ha : Model.FastRepresents m0 2368 (p + 2) a)
    (hm : Model.FastRepresents m0 0 (p + 2) mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord m0 (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord m0 2720).toNat + 1) % 2 ^ 256 = 0)
    (hz : Monpro.tValue m0 (p + 2) = 0) :
    ∃ Q, Q < Limbs.radix ^ (p + 2) ∧
      Monpro.tValue (SquareModel.sqRowsMem m0 (p + 2) (p + 2)) (p + 2) *
          Limbs.radix ^ (p + 2) = a * a + Q * mm ∧
      Monpro.tValue (SquareModel.sqRowsMem m0 (p + 2) (p + 2)) (p + 2) <
          Limbs.radix ^ (p + 2) + mm ∧
      Monpro.tValue (SquareModel.sqRowsMem m0 (p + 2) (p + 2)) (p + 2) <
          2 * Limbs.radix ^ (p + 2) := by
  obtain ⟨Q, hQ, hinv⟩ := SquareModel.sqRows_invariant m0 p mm hn32 hm hminv hz (p + 2) le_rfl
  have hlimb : ∀ k, SquareModel.aLimbs m0 (p + 2) k < 2 * 2 ^ 255 := by
    intro k
    rw [SquareModel.two_half_radix]
    exact Monpro.word_lt_size _
  have hsq := SquareMath.square_identity (h := 2 ^ 255) (by norm_num)
    (SquareModel.aLimbs m0 (p + 2)) hlimb (p + 2)
  rw [SquareModel.two_half_radix] at hsq
  have hA : Monpro.limbSum (SquareModel.aLimbs m0 (p + 2)) (p + 2) = a :=
    Monpro.limbSum_fastRepresents ha
  rw [hsq, SquareModel.lsum_radix, hA, sq] at hinv
  have hR : 0 < Limbs.radix ^ (p + 2) := pow_pos Limbs.radix_pos _
  have heq : Monpro.tValue (SquareModel.sqRowsMem m0 (p + 2) (p + 2)) (p + 2) =
      redc (Limbs.radix ^ (p + 2)) mm a a Q := by
    unfold redc
    rw [← hinv, Nat.mul_div_assoc _ (dvd_refl _), Nat.div_self hR, Nat.mul_one]
  have hb := redc_radix_bounds hmpos hm.1 ha.1 ha.1 hQ
  refine ⟨Q, hQ, hinv, ?_, ?_⟩
  · rw [heq]
    exact hb.1
  · rw [heq]
    exact hb.1.trans hb.2

theorem current_sqRows_lazy_tn_le_one (m0 : ByteArray) (p a mm : Nat) (hn32 : p + 2 ≤ 8)
    (ha : Model.FastRepresents m0 2368 (p + 2) a)
    (hm : Model.FastRepresents m0 0 (p + 2) mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord m0 (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord m0 2720).toNat + 1) % 2 ^ 256 = 0)
    (hz : Monpro.tValue m0 (p + 2) = 0) :
    (MachineState.readWord (SquareModel.sqRowsMem m0 (p + 2) (p + 2)) 2080).toNat ≤ 1 := by
  obtain ⟨_, _, _, _, ht⟩ := current_sqRows_lazy m0 p a mm hn32 ha hm hmpos hminv hz
  exact top_limb_le_one
    (low := Csub.lowValue (SquareModel.sqRowsMem m0 (p + 2) (p + 2)) 2112 (p + 2) (p + 2))
    ht rfl

theorem redc_mixed_lt {R m a b q k : Nat} (hR : 0 < R) (hm : 0 < m)
    (ha : a < R) (hb : b < k * m) (hq : q < R) :
    redc R m a b q < (k + 1) * m := by
  unfold redc
  apply (Nat.div_lt_iff_lt_mul hR).2
  have hp : a * b < R * (k * m) :=
    lt_of_le_of_lt (Nat.mul_le_mul_right b (Nat.le_of_lt ha))
      (Nat.mul_lt_mul_of_pos_left hb hR)
  have hq' : q * m < R * m := Nat.mul_lt_mul_of_pos_right hq hm
  nlinarith

theorem redc_mixed_canonical_lt_two {R m a b q : Nat} (hR : 0 < R) (hm : 0 < m)
    (ha : a < R) (hb : b < m) (hq : q < R) : redc R m a b q < 2 * m := by
  have hb' : b < 1 * m := by simpa using hb
  simpa using redc_mixed_lt hR hm ha hb' hq

end Challenge.Modexp.Submission.Proofs.Fast.LazyBounds
