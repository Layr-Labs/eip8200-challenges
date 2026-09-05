import Mathlib.Tactic
import Challenge.Modexp.Submission.Proofs.Montgomery.CIOS

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Montgomery.Domain

open Challenge.Modexp.Submission.Proofs.Montgomery.CIOS

def R (n : Nat) : Nat := B ^ n

def encode (m n x : Nat) : Nat := (x * R n) % m

def mont (m np n a b : Nat) : Nat := reduce (run a b m np n) m

private theorem encode_lt (m n x : Nat) (hm : 0 < m) :
    encode m n x < m := by
  unfold encode
  exact Nat.mod_lt _ hm

private theorem encode_modEq (m n x : Nat) :
    encode m n x ≡ x * R n [MOD m] := by
  simpa [encode] using Nat.mod_modEq (x * R n) m

private theorem encode_mul_modEq (m n x y : Nat) :
    encode m n x * encode m n y ≡
      (x * y * R n) * R n [MOD m] := by
  convert (encode_modEq m n x).mul (encode_modEq m n y) using 1
  · ring

private theorem mont_contract_modEq (m np n a b : Nat)
    (hm : 0 < m) (hb : b ≤ m) (ha : a < R n)
    (hinv : (m * np + 1) % B = 0) :
    mont m np n a b < m ∧
      mont m np n a b * R n ≡ a * b [MOD m] := by
  have h := normalized_contract_of_le a b m np n hm hb ha hinv
  constructor
  · simpa [mont] using h.1
  · simpa [mont, R, Nat.ModEq] using h.2

private theorem eq_of_modEq_of_lt {a b m : Nat}
    (ha : a < m) (hb : b < m) (h : a ≡ b [MOD m]) : a = b := by
  change a % m = b % m at h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

theorem mont_encode_mul (m np n x y : Nat)
    (hm : 0 < m) (hmR : m < R n) (hcop : Nat.Coprime m (R n))
    (hinv : (m * np + 1) % B = 0) :
    mont m np n (encode m n x) (encode m n y) = encode m n (x * y) := by
  have ha : encode m n x < R n := (encode_lt m n x hm).trans hmR
  have hb : encode m n y ≤ m := (encode_lt m n y hm).le
  have hcontract := mont_contract_modEq m np n
    (encode m n x) (encode m n y) hm hb ha hinv
  have hright :
      mont m np n (encode m n x) (encode m n y) * R n ≡
        encode m n (x * y) * R n [MOD m] := by
    calc
      mont m np n (encode m n x) (encode m n y) * R n ≡
          encode m n x * encode m n y [MOD m] := hcontract.2
      _ ≡ (x * y * R n) * R n [MOD m] := encode_mul_modEq m n x y
      _ ≡ encode m n (x * y) * R n [MOD m] :=
        ((encode_modEq m n (x * y)).mul_right (R n)).symm
  apply eq_of_modEq_of_lt hcontract.1 (encode_lt m n (x * y) hm)
  exact Nat.ModEq.cancel_right_of_coprime hcop hright

theorem mont_decode (m np n x : Nat)
    (hm : 0 < m) (hmR : m < R n) (hcop : Nat.Coprime m (R n))
    (hinv : (m * np + 1) % B = 0) :
    mont m np n (encode m n x) 1 = x % m := by
  have ha : encode m n x < R n := (encode_lt m n x hm).trans hmR
  have hcontract := mont_contract_modEq m np n
    (encode m n x) 1 hm (by omega) ha hinv
  have hright :
      mont m np n (encode m n x) 1 * R n ≡ x * R n [MOD m] := by
    calc
      mont m np n (encode m n x) 1 * R n ≡ encode m n x * 1 [MOD m] :=
        hcontract.2
      _ ≡ x * R n [MOD m] := by simpa using encode_modEq m n x
  have hcancel : mont m np n (encode m n x) 1 ≡ x [MOD m] :=
    Nat.ModEq.cancel_right_of_coprime hcop hright
  change mont m np n (encode m n x) 1 % m = x % m at hcancel
  rw [Nat.mod_eq_of_lt hcontract.1] at hcancel
  exact hcancel

theorem mont_encode_input (m np n x : Nat)
    (hm : 0 < m) (_hmR : m < R n) (hcop : Nat.Coprime m (R n))
    (hx : x < R n) (hinv : (m * np + 1) % B = 0) :
    mont m np n x (encode m n (R n)) = encode m n x := by
  have hb : encode m n (R n) ≤ m := (encode_lt m n (R n) hm).le
  have hcontract := mont_contract_modEq m np n x
    (encode m n (R n)) hm hb hx hinv
  have hright :
      mont m np n x (encode m n (R n)) * R n ≡
        encode m n x * R n [MOD m] := by
    calc
      mont m np n x (encode m n (R n)) * R n ≡
          x * encode m n (R n) [MOD m] := hcontract.2
      _ ≡ x * (R n * R n) [MOD m] :=
        (encode_modEq m n (R n)).mul_left x
      _ ≡ (x * R n) * R n [MOD m] := by
        change (x * (R n * R n)) % m = (x * R n * R n) % m
        rw [show x * (R n * R n) = x * R n * R n by ring]
      _ ≡ encode m n x * R n [MOD m] :=
        ((encode_modEq m n x).mul_right (R n)).symm
  apply eq_of_modEq_of_lt hcontract.1 (encode_lt m n x hm)
  exact Nat.ModEq.cancel_right_of_coprime hcop hright

theorem encode_add (m n x y : Nat) (_hm : 0 < m) :
    encode m n (x + y) =
      (encode m n x + encode m n y) % m := by
  unfold encode
  rw [Nat.add_mul, Nat.add_mod]

theorem encode_add_mod (m n x y : Nat) (hm : 0 < m) :
    encode m n ((x + y) % m) =
      (encode m n x + encode m n y) % m := by
  calc
    encode m n ((x + y) % m) = encode m n (x + y) := by
      simp [encode, Nat.mul_mod]
    _ = (encode m n x + encode m n y) % m := encode_add m n x y hm

theorem encode_double (m n x : Nat) (hm : 0 < m) :
    encode m n ((2 * x) % m) = (2 * encode m n x) % m := by
  simpa [two_mul] using encode_add_mod m n x x hm

def square_double_step (m np n p bit : Nat) : Nat :=
  let square := mont m np n (encode m n (2 ^ p)) (encode m n (2 ^ p))
  if bit = 0 then square else (square + square) % m

theorem square_double_step_correct (m np n p bit : Nat)
    (hm : 0 < m) (hmR : m < R n) (hcop : Nat.Coprime m (R n))
    (hbit : bit = 0 ∨ bit = 1)
    (hinv : (m * np + 1) % B = 0) :
    square_double_step m np n p bit =
      encode m n (2 ^ (2 * p + bit)) := by
  have hsquare := mont_encode_mul m np n (2 ^ p) (2 ^ p)
    hm hmR hcop hinv
  have hpow : 2 ^ p * 2 ^ p = 2 ^ (2 * p) := by
    calc
      2 ^ p * 2 ^ p = 2 ^ (p + p) := (pow_add 2 p p).symm
      _ = 2 ^ (2 * p) := by
        congr 1
        omega
  unfold square_double_step
  dsimp
  by_cases hzero : bit = 0
  · subst bit
    simp only [Nat.add_zero]
    simpa [hpow] using hsquare
  · have hone : bit = 1 := hbit.resolve_left hzero
    subst bit
    simp only [if_neg (by decide : ¬(1 : Nat) = 0)]
    rw [hsquare, hpow]
    have hadd := encode_add_mod m n (2 ^ (2 * p)) (2 ^ (2 * p)) hm
    rw [← hadd]
    have hexp : 2 ^ (2 * p) + 2 ^ (2 * p) = 2 ^ (2 * p + 1) := by
      calc
        2 ^ (2 * p) + 2 ^ (2 * p) = 2 * 2 ^ (2 * p) := by ring
        _ = 2 ^ (2 * p + 1) := by rw [pow_succ]; ring
    rw [hexp]
    simp [encode, Nat.mul_mod]

theorem coprime_R_of_odd (m n : Nat) (_hm : 0 < m)
    (hodd : m % 2 = 1) : Nat.Coprime m (R n) := by
  have hm2 : Nat.Coprime m 2 :=
    (Nat.coprime_two_right).2 (Nat.odd_iff.mpr hodd)
  have hB : Nat.Coprime m B := by
    rw [B, Nat.coprime_pow_right_iff (by norm_num : 0 < (256 : Nat))]
    exact hm2
  by_cases hn : n = 0
  · simp [R, hn]
  · rw [R, Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hn)]
    exact hB

theorem inverse_lift (m np : Nat)
    (h : (m % B * np + 1) % B = 0) :
    (m * np + 1) % B = 0 := by
  have hlow : m % B * np + 1 ≡ 0 [MOD B] := by
    change (m % B * np + 1) % B = 0 % B
    simpa using h
  have hreplace : m % B * np + 1 ≡ m * np + 1 [MOD B] := by
    simpa using (Nat.mod_modEq m B).mul_right np |>.add_right 1
  have hfull : m * np + 1 ≡ 0 [MOD B] := hreplace.symm.trans hlow
  simpa [Nat.ModEq] using hfull

end Challenge.Modexp.Submission.Proofs.Montgomery.Domain
