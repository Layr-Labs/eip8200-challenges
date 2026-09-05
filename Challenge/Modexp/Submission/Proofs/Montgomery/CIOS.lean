import Mathlib.Tactic

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Montgomery.CIOS

def B : Nat := 2 ^ 256

private theorem B_pos : 0 < B := by norm_num [B]

/-- Montgomery quotient selected from the low input limb. -/
def quotient (value nprime : Nat) : Nat := (value % B * nprime) % B

theorem quotient_lt (value nprime : Nat) : quotient value nprime < B := by
  exact Nat.mod_lt _ B_pos

/-- The selected quotient cancels the low radix limb. -/
theorem add_quotient_mod_eq_zero (value modulus nprime : Nat)
    (hinv : (modulus * nprime + 1) % B = 0) :
    (value + quotient value nprime * modulus) % B = 0 := by
  have hinv' : (1 + nprime * modulus) % B = 0 := by
    simpa [Nat.add_comm, Nat.mul_comm] using hinv
  have hv : value ≡ value % B [MOD B] :=
    (Nat.mod_modEq value B).symm
  have hq : quotient value nprime ≡ value % B * nprime [MOD B] := by
    exact Nat.mod_modEq (value % B * nprime) B
  have hadd := hv.add (hq.mul_right modulus)
  have hfactor : value % B + value % B * nprime * modulus =
      value % B * (1 + nprime * modulus) := by ring
  rw [hfactor] at hadd
  have hzero : 1 + nprime * modulus ≡ 0 [MOD B] := by
    exact hinv'
  have hmul := hzero.mul_left (value % B)
  have hfinal := hadd.trans hmul
  exact hfinal

/-- One integrated operand-scanning Montgomery recurrence step. -/
def step (acc digit multiplicand modulus nprime : Nat) : Nat :=
  let value := acc + digit * multiplicand
  (value + quotient value nprime * modulus) / B

theorem step_lt_two_modulus_of_le {acc digit multiplicand modulus nprime : Nat}
    (hmodulus : 0 < modulus) (hacc : acc < 2 * modulus)
    (hdigit : digit < B) (hmultiplicand : multiplicand ≤ modulus) :
    step acc digit multiplicand modulus nprime < 2 * modulus := by
  let value := acc + digit * multiplicand
  let q := quotient value nprime
  have haccLe : acc ≤ 2 * modulus - 1 := by omega
  have hdigitLe : digit ≤ B - 1 := by omega
  have hqLt : q < B := quotient_lt value nprime
  have hqLe : q ≤ B - 1 := by omega
  have hproduct : digit * multiplicand ≤ (B - 1) * modulus :=
    Nat.mul_le_mul hdigitLe hmultiplicand
  have hqProduct : q * modulus ≤ (B - 1) * modulus :=
    Nat.mul_le_mul hqLe (Nat.le_refl modulus)
  have hnum : value + q * modulus ≤ 2 * B * modulus - 1 := by
    dsimp only [value]
    dsimp only [B] at hproduct hqProduct ⊢
    omega
  change (value + q * modulus) / B < 2 * modulus
  rw [Nat.div_lt_iff_lt_mul B_pos]
  calc
    value + q * modulus ≤ 2 * B * modulus - 1 := hnum
    _ < 2 * modulus * B := by
      dsimp only [B]
      omega

theorem step_lt_two_modulus {acc digit multiplicand modulus nprime : Nat}
    (hmodulus : 0 < modulus) (hacc : acc < 2 * modulus)
    (hdigit : digit < B) (hmultiplicand : multiplicand < modulus) :
    step acc digit multiplicand modulus nprime < 2 * modulus := by
  exact step_lt_two_modulus_of_le hmodulus hacc hdigit hmultiplicand.le

/-- The finite CIOS recurrence, scanning the input from its low limb. -/
def run (a b modulus nprime : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => step (run a b modulus nprime i) ((a / B ^ i) % B) b modulus nprime

theorem step_mul_eq {acc digit multiplicand modulus nprime : Nat}
    (hinv : (modulus * nprime + 1) % B = 0) :
    B * step acc digit multiplicand modulus nprime =
      acc + digit * multiplicand + quotient (acc + digit * multiplicand) nprime * modulus := by
  let value := acc + digit * multiplicand
  let q := quotient value nprime
  have hzero : (value + q * modulus) % B = 0 := by
    exact add_quotient_mod_eq_zero value modulus nprime hinv
  have hdecomp := Nat.mod_add_div (value + q * modulus) B
  change B * ((value + q * modulus) / B) = value + q * modulus
  omega

theorem pow_succ_prefix (a : Nat) (i : Nat) :
    a % B ^ (i + 1) = a % B ^ i + B ^ i * ((a / B ^ i) % B) := by
  rw [Nat.pow_succ, Nat.mod_mul]

theorem step_mul_modEq {acc digit multiplicand modulus nprime : Nat}
    (hinv : (modulus * nprime + 1) % B = 0) :
    step acc digit multiplicand modulus nprime * B ≡
      acc + digit * multiplicand [MOD modulus] := by
  rw [Nat.ModEq, Nat.mul_comm, step_mul_eq hinv, Nat.add_mul_mod_self_right]

theorem run_invariant (a b modulus nprime : Nat)
    (hinv : (modulus * nprime + 1) % B = 0) (i : Nat) :
    run a b modulus nprime i * B ^ i ≡
      (a % B ^ i) * b [MOD modulus] := by
  induction i with
  | zero =>
    simp [run, Nat.ModEq, Nat.mod_one]
  | succ i ih =>
    let acc := run a b modulus nprime i
    let digit := (a / B ^ i) % B
    have hstep : step acc digit b modulus nprime * B ≡
        acc + digit * b [MOD modulus] := by
      exact step_mul_modEq hinv
    have hdist₁ : (acc + digit * b) * B ^ i =
        acc * B ^ i + (B ^ i * digit) * b := by
      ring
    have hdist₂ : (a % B ^ i + B ^ i * digit) * b =
        (a % B ^ i) * b + (B ^ i * digit) * b := by
      ring
    have hinner : (acc + digit * b) * B ^ i ≡
        (a % B ^ i + B ^ i * digit) * b [MOD modulus] := by
      calc
        (acc + digit * b) * B ^ i ≡
            acc * B ^ i + (B ^ i * digit) * b [MOD modulus] := by
          rw [hdist₁]
        _ ≡ (a % B ^ i) * b + (B ^ i * digit) * b [MOD modulus] :=
          ih.add (Nat.ModEq.refl _)
        _ ≡ (a % B ^ i + B ^ i * digit) * b [MOD modulus] := by
          rw [hdist₂]
    have hprefix : a % B ^ (i + 1) =
        a % B ^ i + B ^ i * digit := by
      exact pow_succ_prefix a i
    change step acc digit b modulus nprime * B ^ (i + 1) ≡
      (a % B ^ (i + 1)) * b [MOD modulus]
    calc
      step acc digit b modulus nprime * B ^ (i + 1) ≡
          (step acc digit b modulus nprime * B) * B ^ i [MOD modulus] := by
        rw [Nat.pow_succ]
        have heq : step acc digit b modulus nprime * (B ^ i * B) =
            (step acc digit b modulus nprime * B) * B ^ i := by
          ring
        rw [heq]
      _ ≡ (acc + digit * b) * B ^ i [MOD modulus] :=
        hstep.mul_right _
      _ ≡ (a % B ^ i + B ^ i * digit) * b [MOD modulus] := hinner
      _ ≡ (a % B ^ (i + 1)) * b [MOD modulus] := by
        rw [hprefix]

theorem run_lt_two_modulus_of_le (a b modulus nprime n : Nat)
    (hmodulus : 0 < modulus) (hb : b ≤ modulus) :
    run a b modulus nprime n < 2 * modulus := by
  induction n with
  | zero =>
    simp [run]
    omega
  | succ n ih =>
    change step (run a b modulus nprime n) ((a / B ^ n) % B)
        b modulus nprime < 2 * modulus
    exact step_lt_two_modulus_of_le hmodulus ih (Nat.mod_lt _ B_pos) hb

theorem run_lt_two_modulus (a b modulus nprime n : Nat)
    (hmodulus : 0 < modulus) (hb : b < modulus) :
    run a b modulus nprime n < 2 * modulus := by
  exact run_lt_two_modulus_of_le a b modulus nprime n hmodulus hb.le

theorem run_congruence (a b modulus nprime n : Nat)
    (ha : a < B ^ n) (hinv : (modulus * nprime + 1) % B = 0) :
    (run a b modulus nprime n * B ^ n) % modulus = (a * b) % modulus := by
  have h := run_invariant a b modulus nprime hinv n
  have ha' : a % B ^ n = a := Nat.mod_eq_of_lt ha
  rw [Nat.ModEq, ha'] at h
  exact h

theorem run_contract_of_le (a b modulus nprime n : Nat)
    (hmodulus : 0 < modulus) (hb : b ≤ modulus)
    (ha : a < B ^ n) (hinv : (modulus * nprime + 1) % B = 0) :
    run a b modulus nprime n < 2 * modulus ∧
      (run a b modulus nprime n * B ^ n) % modulus = (a * b) % modulus := by
  exact ⟨run_lt_two_modulus_of_le a b modulus nprime n hmodulus hb,
    run_congruence a b modulus nprime n ha hinv⟩

theorem run_contract (a b modulus nprime n : Nat)
    (hmodulus : 0 < modulus) (hb : b < modulus)
    (ha : a < B ^ n) (hinv : (modulus * nprime + 1) % B = 0) :
    run a b modulus nprime n < 2 * modulus ∧
      (run a b modulus nprime n * B ^ n) % modulus = (a * b) % modulus := by
  exact run_contract_of_le a b modulus nprime n hmodulus hb.le ha hinv

/-- The one-subtraction final normalization used after a CIOS run. -/
def reduce (t modulus : Nat) : Nat := if modulus ≤ t then t - modulus else t

theorem reduce_eq_mod {t modulus : Nat}
    (_hmodulus : 0 < modulus) (ht : t < 2 * modulus) :
    reduce t modulus = t % modulus := by
  unfold reduce
  by_cases hle : modulus ≤ t
  · rw [if_pos hle]
    have hlt : t - modulus < modulus := by omega
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt]
  · rw [if_neg hle]
    have hlt : t < modulus := by omega
    rw [Nat.mod_eq_of_lt hlt]

theorem reduce_contract {t modulus : Nat}
    (hmodulus : 0 < modulus) (ht : t < 2 * modulus) :
    reduce t modulus < modulus ∧ reduce t modulus ≡ t [MOD modulus] := by
  have heq := reduce_eq_mod hmodulus ht
  constructor
  · rw [heq]
    exact Nat.mod_lt _ hmodulus
  · rw [heq]
    exact Nat.mod_modEq t modulus

theorem normalized_contract_of_le (a b modulus nprime n : Nat)
    (hmodulus : 0 < modulus) (hb : b ≤ modulus)
    (ha : a < B ^ n) (hinv : (modulus * nprime + 1) % B = 0) :
    reduce (run a b modulus nprime n) modulus < modulus ∧
      (reduce (run a b modulus nprime n) modulus * B ^ n) % modulus =
        (a * b) % modulus := by
  have hrun := run_contract_of_le a b modulus nprime n hmodulus hb ha hinv
  have hreduce := reduce_eq_mod hmodulus hrun.1
  constructor
  · rw [hreduce]
    exact Nat.mod_lt _ hmodulus
  · rw [hreduce]
    simpa only [Nat.mod_mul_mod] using hrun.2

theorem normalized_contract (a b modulus nprime n : Nat)
    (hmodulus : 0 < modulus) (hb : b < modulus)
    (ha : a < B ^ n) (hinv : (modulus * nprime + 1) % B = 0) :
    reduce (run a b modulus nprime n) modulus < modulus ∧
      (reduce (run a b modulus nprime n) modulus * B ^ n) % modulus =
        (a * b) % modulus := by
  exact normalized_contract_of_le a b modulus nprime n hmodulus hb.le ha hinv

end Challenge.Modexp.Submission.Proofs.Montgomery.CIOS
