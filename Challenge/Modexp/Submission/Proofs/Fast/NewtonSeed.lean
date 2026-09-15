import Challenge.Modexp.Submission.Proofs.Fast.Model

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.NewtonSeed

open Challenge.Modexp.Submission.Proofs

/-- The low-bit inverse seed, evaluated with the EVM's word multiplication. -/
def seed (m : Nat) : Nat := (3 * m % Limbs.radix) ^^^ 2

theorem word_seed (m : Nat) :
    EvmSemantics.UInt256.xor (EvmSemantics.UInt256.ofNat 2)
      (EvmSemantics.UInt256.ofNat 3 * EvmSemantics.UInt256.ofNat m) =
      EvmSemantics.UInt256.ofNat (seed m) := by
  change EvmSemantics.UInt256.mk _ = EvmSemantics.UInt256.mk _
  congr 1
  apply Fin.ext
  change ((2 % Limbs.radix) ^^^
    (((3 % Limbs.radix) * (m % Limbs.radix)) % Limbs.radix)) % Limbs.radix =
      seed m % Limbs.radix
  rw [← Nat.mul_mod, Nat.xor_comm]
  rfl

def iter (m : Nat) : Nat → Nat
  | 0 => seed m
  | k + 1 => Model.newtonStep m (iter m k)

/-- Four correct bits are enough for six doublings of precision. -/
theorem seed_spec {m : Nat} (hodd : m % 2 = 1) : m * seed m % 16 = 1 := by
  have small : ∀ a : Fin 16, a.val % 2 = 1 →
      a.val * (((3 * a.val) % 16) ^^^ 2) % 16 = 1 := by decide
  have trunc (a : Nat) : a % Limbs.radix % 16 = a % 16 :=
    Nat.mod_mod_of_dvd a (by decide)
  have hs : seed m % 16 = ((3 * (m % 16)) % 16) ^^^ 2 := by
    unfold seed
    rw [show 16 = 2 ^ 4 by decide, Nat.xor_mod_two_pow]
    change ((3 * m % Limbs.radix) % 16 ^^^ 2) = _
    rw [trunc, Nat.mul_mod]
    rfl
  rw [Nat.mul_mod, hs]
  apply small ⟨m % 16, Nat.mod_lt _ (by decide)⟩
  change m % 16 % 2 = 1
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)]
  exact hodd

theorem iter_spec {m : Nat} (hodd : m % 2 = 1) :
    ∀ j, j ≤ 6 → m * iter m j % 2 ^ (2 ^ (j + 2)) = 1 % 2 ^ (2 ^ (j + 2))
  | 0, _ => by
      change m * seed m % 16 = 1
      exact seed_spec hodd
  | j + 1, hj => by
      have ih := iter_spec hodd j (by omega)
      have hk : 2 * 2 ^ (j + 2) ≤ 256 := by
        have h : 2 ^ (j + 3) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
        rw [show j + 3 = (j + 2) + 1 by omega, pow_succ] at h
        omega
      have h := Model.newton_step_nat hk ih (Model.newtonStep_modEq m (iter m j))
      change m * Model.newtonStep m (iter m j) % 2 ^ (2 ^ ((j + 2) + 1)) =
        1 % 2 ^ (2 ^ ((j + 2) + 1))
      rw [pow_succ, Nat.mul_comm (2 ^ (j + 2)) 2]
      exact h

theorem six_spec {m : Nat} (hodd : m % 2 = 1) :
    m * iter m 6 % Limbs.radix = 1 := by
  exact iter_spec hodd 6 le_rfl

theorem inverse_unique (m a b : Nat) (ha : a < Limbs.radix) (hb : b < Limbs.radix)
    (hia : m * a % Limbs.radix = 1) (hib : m * b % Limbs.radix = 1) : a = b := by
  calc a = (a * (m * b)) % Limbs.radix := by
        rw [Nat.mul_mod, hib, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt ha]
      _ = ((m * a) * b) % Limbs.radix := by
        congr 1
        ring
      _ = b := by
        rw [Nat.mul_mod, hia, Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hb]

/-- The shorter computation gives exactly the previously proved word inverse. -/
theorem six_eq_old {m : Nat} (hodd : m % 2 = 1) :
    iter m 6 = Model.newtonIter m 8 :=
  inverse_unique m _ _ (Model.newtonStep_lt _ _) (Model.newtonStep_lt _ _)
    (six_spec hodd) (Model.newtonIter_eight hodd)

end Challenge.Modexp.Submission.Proofs.Fast.NewtonSeed
