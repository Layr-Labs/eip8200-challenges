import Challenge.Modexp.Submission.Proofs.Fast.Model

set_option warningAsError true

/-!
# Arithmetic for the direct RR leading-one handover

This module is deliberately independent of the executable fast-path proof.
It isolates the width-counter identity and the Montgomery suffix recurrence
needed by the direct CC-to-RR handover.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.RrLeadingLogic

open Challenge.Modexp.Submission.Proofs

/-- The bit consumed at position `k`, stated without importing `Fast.Exp`. -/
def bitAt (value k : Nat) : Nat := value / 2 ^ k % 2

theorem bitAt_le_one (value k : Nat) : bitAt value k ≤ 1 := by
  unfold bitAt
  have := Nat.mod_lt (value / 2 ^ k) (by decide : 0 < 2)
  omega

/-- A comparison result represented as the natural word `0` or `1`. -/
def ltWord (threshold value : Nat) : Nat :=
  if threshold < value then 1 else 0

/-- Branch-free RR counter left after the leading one has been consumed. -/
def directCounter (n : Nat) : Nat :=
  ltWord 3 n + ltWord 7 n + ltWord 15 n + ltWord 31 n

theorem directCounter_formula (n : Nat) :
    directCounter n =
      (if 3 < n then 1 else 0) + (if 7 < n then 1 else 0) +
        (if 15 < n then 1 else 0) + (if 31 < n then 1 else 0) := by
  rfl

/-- The direct counter always fits the inherited RR counter range. -/
theorem directCounter_le_four {n : Nat} (_hn2 : 2 ≤ n) (_hn32 : n ≤ 32) :
    directCounter n ≤ 4 := by
  interval_cases n <;> norm_num [directCounter, ltWord]

/-- Explicit interval form used by the EVM counter-state bridge. -/
theorem directCounter_range {n : Nat} (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    0 ≤ directCounter n ∧ directCounter n ≤ 4 := by
  exact ⟨Nat.zero_le _, directCounter_le_four hn2 hn32⟩

/-- The counter points immediately below the unique consumed leading bit. -/
theorem directCounter_leading_prefix {n : Nat} (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    Model.expPrefix n (directCounter n + 1) = 1 := by
  interval_cases n <;> norm_num [directCounter, ltWord, Model.expPrefix]

/-- The next higher prefix is zero, so the prefix above is genuinely leading. -/
theorem directCounter_higher_prefix_zero {n : Nat} (hn2 : 2 ≤ n)
    (hn32 : n ≤ 32) :
    Model.expPrefix n (directCounter n + 2) = 0 := by
  interval_cases n <;> norm_num [directCounter, ltWord, Model.expPrefix]

theorem directCounter_leading_bit {n : Nat} (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    bitAt n (directCounter n + 1) = 1 := by
  interval_cases n <;> norm_num [directCounter, ltWord, bitAt]

/-- Montgomery square-and-multiply over the remaining bits `start, ..., 0`.
The initial value already represents the prefix above `start`. -/
def rrSuffixValue (mm R n start initial : Nat) : Nat → Nat
  | 0 => initial
  | i + 1 =>
      Model.montMul mm R
        (Model.montMul mm R
          (rrSuffixValue mm R n start initial i)
          (rrSuffixValue mm R n start initial i))
        (if bitAt n (start - i) = 0 then R % mm
          else Limbs.radix * R % mm)

theorem rrSuffixValue_succ (mm R n start initial i : Nat) :
    rrSuffixValue mm R n start initial (i + 1) =
      Model.montMul mm R
        (Model.montMul mm R
          (rrSuffixValue mm R n start initial i)
          (rrSuffixValue mm R n start initial i))
        (if bitAt n (start - i) = 0 then R % mm
          else Limbs.radix * R % mm) := by
  rfl

/-- General suffix invariant: after `i` remaining-bit steps, the accumulator
represents the prefix ending just above bit `start - i`. -/
theorem rrSuffixValue_form {mm R n start initial : Nat}
    (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hinitial : initial ≡
      Limbs.radix ^ (Model.expPrefix n (start + 1)) * R [MOD mm]) :
    ∀ i, i ≤ start + 1 →
      rrSuffixValue mm R n start initial i ≡
        Limbs.radix ^ (Model.expPrefix n (start + 1 - i)) * R [MOD mm] := by
  intro i
  induction i with
  | zero =>
      intro _
      change initial ≡
        Limbs.radix ^ (Model.expPrefix n (start + 1)) * R [MOD mm]
      exact hinitial
  | succ i ih =>
      intro hi
      have hiStart : i ≤ start := by omega
      have hv := ih (by omega)
      have hsq := Model.montMul_form hm hcop hv hv
      have hpow :
          Limbs.radix ^ (Model.expPrefix n (start + 1 - i)) *
              Limbs.radix ^ (Model.expPrefix n (start + 1 - i)) =
            Limbs.radix ^ (2 * Model.expPrefix n (start + 1 - i)) := by
        rw [two_mul, pow_add]
      have hx :
          Limbs.radix ^ (Model.expPrefix n (start + 1 - i)) *
                Limbs.radix ^ (Model.expPrefix n (start + 1 - i)) * R % mm ≡
            Limbs.radix ^ (2 * Model.expPrefix n (start + 1 - i)) * R [MOD mm] := by
        rw [hpow]
        exact Nat.mod_modEq _ mm
      have hsel :
          (if bitAt n (start - i) = 0 then R % mm
            else Limbs.radix * R % mm) ≡
          Limbs.radix ^ (bitAt n (start - i)) * R [MOD mm] := by
        by_cases hzero : bitAt n (start - i) = 0
        · rw [if_pos hzero, hzero, pow_zero, one_mul]
          exact Nat.mod_modEq R mm
        · have hone : bitAt n (start - i) = 1 := by
            have := bitAt_le_one n (start - i)
            omega
          rw [if_neg hzero, hone, pow_one]
          exact Nat.mod_modEq _ mm
      have hstep :
          Model.expPrefix n (start + 1 - (i + 1)) =
            2 * Model.expPrefix n (start + 1 - i) + bitAt n (start - i) := by
        rw [show start + 1 - (i + 1) = start - i by omega,
          show start + 1 - i = start - i + 1 by omega]
        exact Model.expPrefix_succ n (start - i)
      rw [rrSuffixValue_succ, hsq, Model.montMul_form hm hcop hx hsel,
        hstep, pow_add]
      exact Nat.mod_modEq _ mm

/-- Copying `CC = radix * R mod mm` to `RR`, then consuming exactly the
remaining direct-counter bits, reaches the standard `R²` congruence. -/
theorem rrSuffixValue_direct_final {mm R n : Nat}
    (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    rrSuffixValue mm R n (directCounter n) (Limbs.radix * R % mm)
        (directCounter n + 1) ≡
      Limbs.radix ^ n * R [MOD mm] := by
  have hprefix := directCounter_leading_prefix hn2 hn32
  have hinitial : Limbs.radix * R % mm ≡
      Limbs.radix ^ (Model.expPrefix n (directCounter n + 1)) * R [MOD mm] := by
    rw [hprefix, pow_one]
    exact Nat.mod_modEq _ mm
  have h := rrSuffixValue_form hm hcop hinitial
    (directCounter n + 1) le_rfl
  simpa using h

end Challenge.Modexp.Submission.Proofs.Fast.RrLeadingLogic
