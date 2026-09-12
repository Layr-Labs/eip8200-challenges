import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.Modexp.Submission.Proofs.PrimeEval
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Challenge.Modexp.Submission.Proofs.PrimeCertificates
open EvmSemantics EvmSemantics.EVM

def bn254P : Nat := 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

theorem zmod_pow_modPow {a e m : Nat} (hm : 0 < m) :
    (a : ZMod m) ^ e = (Precompile.modPow a e m : ZMod m) := by
  rw [Algorithm.modPow_eq, if_neg (Nat.ne_of_gt hm)]
  rw [ZMod.natCast_mod]
  exact (Nat.cast_pow a e).symm

theorem zmod_pow_ne_of_modPow_ne {a e m : Nat} (hm : 1 < m)
    (h : Precompile.modPow a e m ≠ 1) :
    (a : ZMod m) ^ e ≠ 1 := by
  rw [zmod_pow_modPow (by omega)]
  intro he
  have he' : (Precompile.modPow a e m : ZMod m) = (1 : Nat) := by simpa using he
  have heq := (ZMod.natCast_eq_natCast_iff' (Precompile.modPow a e m) 1 m).mp he'
  have hlt : Precompile.modPow a e m < m := Algorithm.modPow_lt (by omega)
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at heq
  exact h heq

theorem prime_dvd_prod_mem {q : Nat} (hq : q.Prime) :
    ∀ (xs : List Nat), (∀ x ∈ xs, x.Prime) → q ∣ xs.prod → q ∈ xs
  | [], hxs, hd => by simp at hd ⊢; exact (hq.ne_one hd).elim
  | x :: xs, hxs, hd => by
      rcases (hq.dvd_mul).mp hd with hx | ht
      · rcases (Nat.dvd_prime (hxs x (by simp))).mp hx with hq1 | hqx
        · exact (hq.ne_one hq1).elim
        · simp [hqx]
      · exact List.mem_cons_of_mem x
          (prime_dvd_prod_mem hq xs (fun y hy => hxs y (by simp [hy])) ht)

theorem lucas_of_factors {p a : Nat} {xs : List Nat}
    (hfactor : p - 1 = xs.prod)
    (hprime : ∀ x ∈ xs, x.Prime)
    (ha : (a : ZMod p) ^ (p - 1) = 1)
    (hneq : ∀ x ∈ xs, (a : ZMod p) ^ ((p - 1) / x) ≠ 1) : p.Prime := by
  apply lucas_primality p a ha
  intro q hq hqd
  apply hneq q (prime_dvd_prod_mem hq xs hprime (hfactor ▸ hqd))

theorem primeCert2 : Nat.Prime 2 := by decide
theorem primeCert3 : Nat.Prime 3 := by decide

theorem primeCert5 : Nat.Prime 5 := by
  apply lucas_of_factors (p := 5) (a := 2) (xs := [2, 2])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact primeCert2
    · exact primeCert2
  · calc
      (2 : ZMod 5) ^ (5 - 1) =
          (Precompile.modPow 2 (5 - 1) 5 : ZMod 5) :=
        zmod_pow_modPow (m := 5) (a := 2) (e := 5 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (5 - 1) 5 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 5) ^ ((5 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((5 - 1) / 2) 5 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact hneq2
    · exact hneq2

theorem primeCert7 : Nat.Prime 7 := by
  apply lucas_of_factors (p := 7) (a := 3) (xs := [2, 3])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact primeCert2
    · exact primeCert3
  · calc
      (3 : ZMod 7) ^ (7 - 1) =
          (Precompile.modPow 3 (7 - 1) 7 : ZMod 7) :=
        zmod_pow_modPow (m := 7) (a := 3) (e := 7 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (7 - 1) 7 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 7) ^ ((7 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((7 - 1) / 2) 7 (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod 7) ^ ((7 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((7 - 1) / 3) 7 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact hneq2
    · exact hneq3

theorem primeCert11 : Nat.Prime 11 := by
  apply lucas_of_factors (p := 11) (a := 2) (xs := [2, 5])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact primeCert2
    · exact primeCert5
  · calc
      (2 : ZMod 11) ^ (11 - 1) =
          (Precompile.modPow 2 (11 - 1) 11 : ZMod 11) :=
        zmod_pow_modPow (m := 11) (a := 2) (e := 11 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (11 - 1) 11 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 11) ^ ((11 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((11 - 1) / 2) 11 (by decide) (by decide)]
      decide
    have hneq5 : (2 : ZMod 11) ^ ((11 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((11 - 1) / 5) 11 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact hneq2
    · exact hneq5

theorem primeCert13 : Nat.Prime 13 := by
  apply lucas_of_factors (p := 13) (a := 2) (xs := [2, 2, 3])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
  · calc
      (2 : ZMod 13) ^ (13 - 1) =
          (Precompile.modPow 2 (13 - 1) 13 : ZMod 13) :=
        zmod_pow_modPow (m := 13) (a := 2) (e := 13 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (13 - 1) 13 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 13) ^ ((13 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((13 - 1) / 2) 13 (by decide) (by decide)]
      decide
    have hneq3 : (2 : ZMod 13) ^ ((13 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((13 - 1) / 3) 13 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq3

theorem primeCert17 : Nat.Prime 17 := by
  apply lucas_of_factors (p := 17) (a := 3) (xs := [2, 2, 2, 2])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
  · calc
      (3 : ZMod 17) ^ (17 - 1) =
          (Precompile.modPow 3 (17 - 1) 17 : ZMod 17) :=
        zmod_pow_modPow (m := 17) (a := 3) (e := 17 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (17 - 1) 17 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 17) ^ ((17 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((17 - 1) / 2) 17 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2

theorem primeCert19 : Nat.Prime 19 := by
  apply lucas_of_factors (p := 19) (a := 2) (xs := [2, 3, 3])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
  · calc
      (2 : ZMod 19) ^ (19 - 1) =
          (Precompile.modPow 2 (19 - 1) 19 : ZMod 19) :=
        zmod_pow_modPow (m := 19) (a := 2) (e := 19 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (19 - 1) 19 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 19) ^ ((19 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((19 - 1) / 2) 19 (by decide) (by decide)]
      decide
    have hneq3 : (2 : ZMod 19) ^ ((19 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((19 - 1) / 3) 19 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq3

theorem primeCert29 : Nat.Prime 29 := by
  apply lucas_of_factors (p := 29) (a := 2) (xs := [2, 2, 7])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert7
  · calc
      (2 : ZMod 29) ^ (29 - 1) =
          (Precompile.modPow 2 (29 - 1) 29 : ZMod 29) :=
        zmod_pow_modPow (m := 29) (a := 2) (e := 29 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (29 - 1) 29 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 29) ^ ((29 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((29 - 1) / 2) 29 (by decide) (by decide)]
      decide
    have hneq7 : (2 : ZMod 29) ^ ((29 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((29 - 1) / 7) 29 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq7

theorem primeCert31 : Nat.Prime 31 := by
  apply lucas_of_factors (p := 31) (a := 3) (xs := [2, 3, 5])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert5
  · calc
      (3 : ZMod 31) ^ (31 - 1) =
          (Precompile.modPow 3 (31 - 1) 31 : ZMod 31) :=
        zmod_pow_modPow (m := 31) (a := 3) (e := 31 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (31 - 1) 31 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 31) ^ ((31 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((31 - 1) / 2) 31 (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod 31) ^ ((31 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((31 - 1) / 3) 31 (by decide) (by decide)]
      decide
    have hneq5 : (3 : ZMod 31) ^ ((31 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((31 - 1) / 5) 31 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq5

theorem primeCert37 : Nat.Prime 37 := by
  apply lucas_of_factors (p := 37) (a := 2) (xs := [2, 2, 3, 3])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
  · calc
      (2 : ZMod 37) ^ (37 - 1) =
          (Precompile.modPow 2 (37 - 1) 37 : ZMod 37) :=
        zmod_pow_modPow (m := 37) (a := 2) (e := 37 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (37 - 1) 37 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 37) ^ ((37 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((37 - 1) / 2) 37 (by decide) (by decide)]
      decide
    have hneq3 : (2 : ZMod 37) ^ ((37 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((37 - 1) / 3) 37 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq3

theorem primeCert41 : Nat.Prime 41 := by
  apply lucas_of_factors (p := 41) (a := 6) (xs := [2, 2, 2, 5])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert5
  · calc
      (6 : ZMod 41) ^ (41 - 1) =
          (Precompile.modPow 6 (41 - 1) 41 : ZMod 41) :=
        zmod_pow_modPow (m := 41) (a := 6) (e := 41 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 6 (41 - 1) 41 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (6 : ZMod 41) ^ ((41 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((41 - 1) / 2) 41 (by decide) (by decide)]
      decide
    have hneq5 : (6 : ZMod 41) ^ ((41 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((41 - 1) / 5) 41 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq5

theorem primeCert67 : Nat.Prime 67 := by
  apply lucas_of_factors (p := 67) (a := 2) (xs := [2, 3, 11])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert11
  · calc
      (2 : ZMod 67) ^ (67 - 1) =
          (Precompile.modPow 2 (67 - 1) 67 : ZMod 67) :=
        zmod_pow_modPow (m := 67) (a := 2) (e := 67 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (67 - 1) 67 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 67) ^ ((67 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((67 - 1) / 2) 67 (by decide) (by decide)]
      decide
    have hneq3 : (2 : ZMod 67) ^ ((67 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((67 - 1) / 3) 67 (by decide) (by decide)]
      decide
    have hneq11 : (2 : ZMod 67) ^ ((67 - 1) / 11) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((67 - 1) / 11) 67 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq11

theorem primeCert73 : Nat.Prime 73 := by
  apply lucas_of_factors (p := 73) (a := 5) (xs := [2, 2, 2, 3, 3])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
  · calc
      (5 : ZMod 73) ^ (73 - 1) =
          (Precompile.modPow 5 (73 - 1) 73 : ZMod 73) :=
        zmod_pow_modPow (m := 73) (a := 5) (e := 73 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 5 (73 - 1) 73 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (5 : ZMod 73) ^ ((73 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((73 - 1) / 2) 73 (by decide) (by decide)]
      decide
    have hneq3 : (5 : ZMod 73) ^ ((73 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((73 - 1) / 3) 73 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq3

theorem primeCert89 : Nat.Prime 89 := by
  apply lucas_of_factors (p := 89) (a := 3) (xs := [2, 2, 2, 11])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert11
  · calc
      (3 : ZMod 89) ^ (89 - 1) =
          (Precompile.modPow 3 (89 - 1) 89 : ZMod 89) :=
        zmod_pow_modPow (m := 89) (a := 3) (e := 89 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (89 - 1) 89 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 89) ^ ((89 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((89 - 1) / 2) 89 (by decide) (by decide)]
      decide
    have hneq11 : (3 : ZMod 89) ^ ((89 - 1) / 11) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((89 - 1) / 11) 89 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq11

theorem primeCert109 : Nat.Prime 109 := by
  apply lucas_of_factors (p := 109) (a := 6) (xs := [2, 2, 3, 3, 3])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
    · exact primeCert3
  · calc
      (6 : ZMod 109) ^ (109 - 1) =
          (Precompile.modPow 6 (109 - 1) 109 : ZMod 109) :=
        zmod_pow_modPow (m := 109) (a := 6) (e := 109 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 6 (109 - 1) 109 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (6 : ZMod 109) ^ ((109 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((109 - 1) / 2) 109 (by decide) (by decide)]
      decide
    have hneq3 : (6 : ZMod 109) ^ ((109 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((109 - 1) / 3) 109 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq3
    · exact hneq3

theorem primeCert127 : Nat.Prime 127 := by
  apply lucas_of_factors (p := 127) (a := 3) (xs := [2, 3, 3, 7])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
    · exact primeCert7
  · calc
      (3 : ZMod 127) ^ (127 - 1) =
          (Precompile.modPow 3 (127 - 1) 127 : ZMod 127) :=
        zmod_pow_modPow (m := 127) (a := 3) (e := 127 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (127 - 1) 127 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 127) ^ ((127 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((127 - 1) / 2) 127 (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod 127) ^ ((127 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((127 - 1) / 3) 127 (by decide) (by decide)]
      decide
    have hneq7 : (3 : ZMod 127) ^ ((127 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((127 - 1) / 7) 127 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq3
    · exact hneq7

theorem primeCert229 : Nat.Prime 229 := by
  apply lucas_of_factors (p := 229) (a := 6) (xs := [2, 2, 3, 19])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert19
  · calc
      (6 : ZMod 229) ^ (229 - 1) =
          (Precompile.modPow 6 (229 - 1) 229 : ZMod 229) :=
        zmod_pow_modPow (m := 229) (a := 6) (e := 229 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 6 (229 - 1) 229 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (6 : ZMod 229) ^ ((229 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((229 - 1) / 2) 229 (by decide) (by decide)]
      decide
    have hneq3 : (6 : ZMod 229) ^ ((229 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((229 - 1) / 3) 229 (by decide) (by decide)]
      decide
    have hneq19 : (6 : ZMod 229) ^ ((229 - 1) / 19) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((229 - 1) / 19) 229 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq19

theorem primeCert233 : Nat.Prime 233 := by
  apply lucas_of_factors (p := 233) (a := 3) (xs := [2, 2, 2, 29])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert29
  · calc
      (3 : ZMod 233) ^ (233 - 1) =
          (Precompile.modPow 3 (233 - 1) 233 : ZMod 233) :=
        zmod_pow_modPow (m := 233) (a := 3) (e := 233 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (233 - 1) 233 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 233) ^ ((233 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((233 - 1) / 2) 233 (by decide) (by decide)]
      decide
    have hneq29 : (3 : ZMod 233) ^ ((233 - 1) / 29) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((233 - 1) / 29) 233 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq29

theorem primeCert271 : Nat.Prime 271 := by
  apply lucas_of_factors (p := 271) (a := 6) (xs := [2, 3, 3, 3, 5])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
    · exact primeCert3
    · exact primeCert5
  · calc
      (6 : ZMod 271) ^ (271 - 1) =
          (Precompile.modPow 6 (271 - 1) 271 : ZMod 271) :=
        zmod_pow_modPow (m := 271) (a := 6) (e := 271 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 6 (271 - 1) 271 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (6 : ZMod 271) ^ ((271 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((271 - 1) / 2) 271 (by decide) (by decide)]
      decide
    have hneq3 : (6 : ZMod 271) ^ ((271 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((271 - 1) / 3) 271 (by decide) (by decide)]
      decide
    have hneq5 : (6 : ZMod 271) ^ ((271 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((271 - 1) / 5) 271 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq3
    · exact hneq3
    · exact hneq5

theorem primeCert311 : Nat.Prime 311 := by
  apply lucas_of_factors (p := 311) (a := 17) (xs := [2, 5, 31])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert5
    · exact primeCert31
  · calc
      (17 : ZMod 311) ^ (311 - 1) =
          (Precompile.modPow 17 (311 - 1) 311 : ZMod 311) :=
        zmod_pow_modPow (m := 311) (a := 17) (e := 311 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 17 (311 - 1) 311 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (17 : ZMod 311) ^ ((311 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((311 - 1) / 2) 311 (by decide) (by decide)]
      decide
    have hneq5 : (17 : ZMod 311) ^ ((311 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((311 - 1) / 5) 311 (by decide) (by decide)]
      decide
    have hneq31 : (17 : ZMod 311) ^ ((311 - 1) / 31) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((311 - 1) / 31) 311 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq5
    · exact hneq31

theorem primeCert491 : Nat.Prime 491 := by
  apply lucas_of_factors (p := 491) (a := 2) (xs := [2, 5, 7, 7])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert5
    · exact primeCert7
    · exact primeCert7
  · calc
      (2 : ZMod 491) ^ (491 - 1) =
          (Precompile.modPow 2 (491 - 1) 491 : ZMod 491) :=
        zmod_pow_modPow (m := 491) (a := 2) (e := 491 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (491 - 1) 491 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 491) ^ ((491 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((491 - 1) / 2) 491 (by decide) (by decide)]
      decide
    have hneq5 : (2 : ZMod 491) ^ ((491 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((491 - 1) / 5) 491 (by decide) (by decide)]
      decide
    have hneq7 : (2 : ZMod 491) ^ ((491 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((491 - 1) / 7) 491 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq5
    · exact hneq7
    · exact hneq7

theorem primeCert911 : Nat.Prime 911 := by
  apply lucas_of_factors (p := 911) (a := 17) (xs := [2, 5, 7, 13])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert5
    · exact primeCert7
    · exact primeCert13
  · calc
      (17 : ZMod 911) ^ (911 - 1) =
          (Precompile.modPow 17 (911 - 1) 911 : ZMod 911) :=
        zmod_pow_modPow (m := 911) (a := 17) (e := 911 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 17 (911 - 1) 911 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (17 : ZMod 911) ^ ((911 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((911 - 1) / 2) 911 (by decide) (by decide)]
      decide
    have hneq5 : (17 : ZMod 911) ^ ((911 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((911 - 1) / 5) 911 (by decide) (by decide)]
      decide
    have hneq7 : (17 : ZMod 911) ^ ((911 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((911 - 1) / 7) 911 (by decide) (by decide)]
      decide
    have hneq13 : (17 : ZMod 911) ^ ((911 - 1) / 13) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((911 - 1) / 13) 911 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq5
    · exact hneq7
    · exact hneq13

theorem primeCert983 : Nat.Prime 983 := by
  apply lucas_of_factors (p := 983) (a := 5) (xs := [2, 491])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact primeCert2
    · exact primeCert491
  · calc
      (5 : ZMod 983) ^ (983 - 1) =
          (Precompile.modPow 5 (983 - 1) 983 : ZMod 983) :=
        zmod_pow_modPow (m := 983) (a := 5) (e := 983 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 5 (983 - 1) 983 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (5 : ZMod 983) ^ ((983 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((983 - 1) / 2) 983 (by decide) (by decide)]
      decide
    have hneq491 : (5 : ZMod 983) ^ ((983 - 1) / 491) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((983 - 1) / 491) 983 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact hneq2
    · exact hneq491

theorem primeCert1231 : Nat.Prime 1231 := by
  apply lucas_of_factors (p := 1231) (a := 3) (xs := [2, 3, 5, 41])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert5
    · exact primeCert41
  · calc
      (3 : ZMod 1231) ^ (1231 - 1) =
          (Precompile.modPow 3 (1231 - 1) 1231 : ZMod 1231) :=
        zmod_pow_modPow (m := 1231) (a := 3) (e := 1231 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (1231 - 1) 1231 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 1231) ^ ((1231 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((1231 - 1) / 2) 1231 (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod 1231) ^ ((1231 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((1231 - 1) / 3) 1231 (by decide) (by decide)]
      decide
    have hneq5 : (3 : ZMod 1231) ^ ((1231 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((1231 - 1) / 5) 1231 (by decide) (by decide)]
      decide
    have hneq41 : (3 : ZMod 1231) ^ ((1231 - 1) / 41) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((1231 - 1) / 41) 1231 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq5
    · exact hneq41

theorem primeCert2221 : Nat.Prime 2221 := by
  apply lucas_of_factors (p := 2221) (a := 2) (xs := [2, 2, 3, 5, 37])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert5
    · exact primeCert37
  · calc
      (2 : ZMod 2221) ^ (2221 - 1) =
          (Precompile.modPow 2 (2221 - 1) 2221 : ZMod 2221) :=
        zmod_pow_modPow (m := 2221) (a := 2) (e := 2221 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (2221 - 1) 2221 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 2221) ^ ((2221 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((2221 - 1) / 2) 2221 (by decide) (by decide)]
      decide
    have hneq3 : (2 : ZMod 2221) ^ ((2221 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((2221 - 1) / 3) 2221 (by decide) (by decide)]
      decide
    have hneq5 : (2 : ZMod 2221) ^ ((2221 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((2221 - 1) / 5) 2221 (by decide) (by decide)]
      decide
    have hneq37 : (2 : ZMod 2221) ^ ((2221 - 1) / 37) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((2221 - 1) / 37) 2221 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq5
    · exact hneq37

theorem primeCert3557 : Nat.Prime 3557 := by
  apply lucas_of_factors (p := 3557) (a := 2) (xs := [2, 2, 7, 127])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert7
    · exact primeCert127
  · calc
      (2 : ZMod 3557) ^ (3557 - 1) =
          (Precompile.modPow 2 (3557 - 1) 3557 : ZMod 3557) :=
        zmod_pow_modPow (m := 3557) (a := 2) (e := 3557 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (3557 - 1) 3557 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 3557) ^ ((3557 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((3557 - 1) / 2) 3557 (by decide) (by decide)]
      decide
    have hneq7 : (2 : ZMod 3557) ^ ((3557 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((3557 - 1) / 7) 3557 (by decide) (by decide)]
      decide
    have hneq127 : (2 : ZMod 3557) ^ ((3557 - 1) / 127) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((3557 - 1) / 127) 3557 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq7
    · exact hneq127

theorem primeCert3691 : Nat.Prime 3691 := by
  apply lucas_of_factors (p := 3691) (a := 2) (xs := [2, 3, 3, 5, 41])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
    · exact primeCert5
    · exact primeCert41
  · calc
      (2 : ZMod 3691) ^ (3691 - 1) =
          (Precompile.modPow 2 (3691 - 1) 3691 : ZMod 3691) :=
        zmod_pow_modPow (m := 3691) (a := 2) (e := 3691 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (3691 - 1) 3691 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 3691) ^ ((3691 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((3691 - 1) / 2) 3691 (by decide) (by decide)]
      decide
    have hneq3 : (2 : ZMod 3691) ^ ((3691 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((3691 - 1) / 3) 3691 (by decide) (by decide)]
      decide
    have hneq5 : (2 : ZMod 3691) ^ ((3691 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((3691 - 1) / 5) 3691 (by decide) (by decide)]
      decide
    have hneq41 : (2 : ZMod 3691) ^ ((3691 - 1) / 41) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((3691 - 1) / 41) 3691 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq3
    · exact hneq5
    · exact hneq41

theorem primeCert4999 : Nat.Prime 4999 := by
  apply lucas_of_factors (p := 4999) (a := 3) (xs := [2, 3, 7, 7, 17])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert7
    · exact primeCert7
    · exact primeCert17
  · calc
      (3 : ZMod 4999) ^ (4999 - 1) =
          (Precompile.modPow 3 (4999 - 1) 4999 : ZMod 4999) :=
        zmod_pow_modPow (m := 4999) (a := 3) (e := 4999 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (4999 - 1) 4999 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 4999) ^ ((4999 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((4999 - 1) / 2) 4999 (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod 4999) ^ ((4999 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((4999 - 1) / 3) 4999 (by decide) (by decide)]
      decide
    have hneq7 : (3 : ZMod 4999) ^ ((4999 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((4999 - 1) / 7) 4999 (by decide) (by decide)]
      decide
    have hneq17 : (3 : ZMod 4999) ^ ((4999 - 1) / 17) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((4999 - 1) / 17) 4999 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq7
    · exact hneq7
    · exact hneq17

theorem primeCert5501 : Nat.Prime 5501 := by
  apply lucas_of_factors (p := 5501) (a := 2) (xs := [2, 2, 5, 5, 5, 11])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert5
    · exact primeCert5
    · exact primeCert5
    · exact primeCert11
  · calc
      (2 : ZMod 5501) ^ (5501 - 1) =
          (Precompile.modPow 2 (5501 - 1) 5501 : ZMod 5501) :=
        zmod_pow_modPow (m := 5501) (a := 2) (e := 5501 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (5501 - 1) 5501 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 5501) ^ ((5501 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((5501 - 1) / 2) 5501 (by decide) (by decide)]
      decide
    have hneq5 : (2 : ZMod 5501) ^ ((5501 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((5501 - 1) / 5) 5501 (by decide) (by decide)]
      decide
    have hneq11 : (2 : ZMod 5501) ^ ((5501 - 1) / 11) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((5501 - 1) / 11) 5501 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq5
    · exact hneq5
    · exact hneq5
    · exact hneq11

theorem primeCert11003 : Nat.Prime 11003 := by
  apply lucas_of_factors (p := 11003) (a := 2) (xs := [2, 5501])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact primeCert2
    · exact primeCert5501
  · calc
      (2 : ZMod 11003) ^ (11003 - 1) =
          (Precompile.modPow 2 (11003 - 1) 11003 : ZMod 11003) :=
        zmod_pow_modPow (m := 11003) (a := 2) (e := 11003 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (11003 - 1) 11003 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 11003) ^ ((11003 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((11003 - 1) / 2) 11003 (by decide) (by decide)]
      decide
    have hneq5501 : (2 : ZMod 11003) ^ ((11003 - 1) / 5501) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((11003 - 1) / 5501) 11003 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact hneq2
    · exact hneq5501

theorem primeCert13327 : Nat.Prime 13327 := by
  apply lucas_of_factors (p := 13327) (a := 3) (xs := [2, 3, 2221])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert2221
  · calc
      (3 : ZMod 13327) ^ (13327 - 1) =
          (Precompile.modPow 3 (13327 - 1) 13327 : ZMod 13327) :=
        zmod_pow_modPow (m := 13327) (a := 3) (e := 13327 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (13327 - 1) 13327 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 13327) ^ ((13327 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((13327 - 1) / 2) 13327 (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod 13327) ^ ((13327 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((13327 - 1) / 3) 13327 (by decide) (by decide)]
      decide
    have hneq2221 : (3 : ZMod 13327) ^ ((13327 - 1) / 2221) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((13327 - 1) / 2221) 13327 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq2221

theorem primeCert327599 : Nat.Prime 327599 := by
  apply lucas_of_factors (p := 327599) (a := 19) (xs := [2, 19, 37, 233])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert19
    · exact primeCert37
    · exact primeCert233
  · calc
      (19 : ZMod 327599) ^ (327599 - 1) =
          (Precompile.modPow 19 (327599 - 1) 327599 : ZMod 327599) :=
        zmod_pow_modPow (m := 327599) (a := 19) (e := 327599 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 19 (327599 - 1) 327599 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (19 : ZMod 327599) ^ ((327599 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 19 ((327599 - 1) / 2) 327599 (by decide) (by decide)]
      decide
    have hneq19 : (19 : ZMod 327599) ^ ((327599 - 1) / 19) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 19 ((327599 - 1) / 19) 327599 (by decide) (by decide)]
      decide
    have hneq37 : (19 : ZMod 327599) ^ ((327599 - 1) / 37) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 19 ((327599 - 1) / 37) 327599 (by decide) (by decide)]
      decide
    have hneq233 : (19 : ZMod 327599) ^ ((327599 - 1) / 233) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 19 ((327599 - 1) / 233) 327599 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq19
    · exact hneq37
    · exact hneq233

theorem primeCert1853641 : Nat.Prime 1853641 := by
  apply lucas_of_factors (p := 1853641) (a := 17) (xs := [2, 2, 2, 3, 3, 5, 19, 271])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
    · exact primeCert5
    · exact primeCert19
    · exact primeCert271
  · calc
      (17 : ZMod 1853641) ^ (1853641 - 1) =
          (Precompile.modPow 17 (1853641 - 1) 1853641 : ZMod 1853641) :=
        zmod_pow_modPow (m := 1853641) (a := 17) (e := 1853641 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 17 (1853641 - 1) 1853641 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (17 : ZMod 1853641) ^ ((1853641 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((1853641 - 1) / 2) 1853641 (by decide) (by decide)]
      decide
    have hneq3 : (17 : ZMod 1853641) ^ ((1853641 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((1853641 - 1) / 3) 1853641 (by decide) (by decide)]
      decide
    have hneq5 : (17 : ZMod 1853641) ^ ((1853641 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((1853641 - 1) / 5) 1853641 (by decide) (by decide)]
      decide
    have hneq19 : (17 : ZMod 1853641) ^ ((1853641 - 1) / 19) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((1853641 - 1) / 19) 1853641 (by decide) (by decide)]
      decide
    have hneq271 : (17 : ZMod 1853641) ^ ((1853641 - 1) / 271) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((1853641 - 1) / 271) 1853641 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq3
    · exact hneq5
    · exact hneq19
    · exact hneq271

theorem primeCert4562087 : Nat.Prime 4562087 := by
  apply lucas_of_factors (p := 4562087) (a := 5) (xs := [2, 17, 109, 1231])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert17
    · exact primeCert109
    · exact primeCert1231
  · calc
      (5 : ZMod 4562087) ^ (4562087 - 1) =
          (Precompile.modPow 5 (4562087 - 1) 4562087 : ZMod 4562087) :=
        zmod_pow_modPow (m := 4562087) (a := 5) (e := 4562087 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 5 (4562087 - 1) 4562087 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (5 : ZMod 4562087) ^ ((4562087 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((4562087 - 1) / 2) 4562087 (by decide) (by decide)]
      decide
    have hneq17 : (5 : ZMod 4562087) ^ ((4562087 - 1) / 17) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((4562087 - 1) / 17) 4562087 (by decide) (by decide)]
      decide
    have hneq109 : (5 : ZMod 4562087) ^ ((4562087 - 1) / 109) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((4562087 - 1) / 109) 4562087 (by decide) (by decide)]
      decide
    have hneq1231 : (5 : ZMod 4562087) ^ ((4562087 - 1) / 1231) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((4562087 - 1) / 1231) 4562087 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq17
    · exact hneq109
    · exact hneq1231

theorem primeCert173171039 : Nat.Prime 173171039 := by
  apply lucas_of_factors (p := 173171039) (a := 13) (xs := [2, 73, 89, 13327])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert73
    · exact primeCert89
    · exact primeCert13327
  · calc
      (13 : ZMod 173171039) ^ (173171039 - 1) =
          (Precompile.modPow 13 (173171039 - 1) 173171039 : ZMod 173171039) :=
        zmod_pow_modPow (m := 173171039) (a := 13) (e := 173171039 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 13 (173171039 - 1) 173171039 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (13 : ZMod 173171039) ^ ((173171039 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 13 ((173171039 - 1) / 2) 173171039 (by decide) (by decide)]
      decide
    have hneq73 : (13 : ZMod 173171039) ^ ((173171039 - 1) / 73) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 13 ((173171039 - 1) / 73) 173171039 (by decide) (by decide)]
      decide
    have hneq89 : (13 : ZMod 173171039) ^ ((173171039 - 1) / 89) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 13 ((173171039 - 1) / 89) 173171039 (by decide) (by decide)]
      decide
    have hneq13327 : (13 : ZMod 173171039) ^ ((173171039 - 1) / 13327) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 13 ((173171039 - 1) / 13327) 173171039 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq73
    · exact hneq89
    · exact hneq13327

theorem primeCert405928799 : Nat.Prime 405928799 := by
  apply lucas_of_factors (p := 405928799) (a := 22) (xs := [2, 11, 3691, 4999])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert11
    · exact primeCert3691
    · exact primeCert4999
  · calc
      (22 : ZMod 405928799) ^ (405928799 - 1) =
          (Precompile.modPow 22 (405928799 - 1) 405928799 : ZMod 405928799) :=
        zmod_pow_modPow (m := 405928799) (a := 22) (e := 405928799 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 22 (405928799 - 1) 405928799 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (22 : ZMod 405928799) ^ ((405928799 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 22 ((405928799 - 1) / 2) 405928799 (by decide) (by decide)]
      decide
    have hneq11 : (22 : ZMod 405928799) ^ ((405928799 - 1) / 11) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 22 ((405928799 - 1) / 11) 405928799 (by decide) (by decide)]
      decide
    have hneq3691 : (22 : ZMod 405928799) ^ ((405928799 - 1) / 3691) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 22 ((405928799 - 1) / 3691) 405928799 (by decide) (by decide)]
      decide
    have hneq4999 : (22 : ZMod 405928799) ^ ((405928799 - 1) / 4999) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 22 ((405928799 - 1) / 4999) 405928799 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq11
    · exact hneq3691
    · exact hneq4999

theorem primeCert1263766531 : Nat.Prime 1263766531 := by
  apply lucas_of_factors (p := 1263766531) (a := 10) (xs := [2, 3, 5, 13, 911, 3557])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert5
    · exact primeCert13
    · exact primeCert911
    · exact primeCert3557
  · calc
      (10 : ZMod 1263766531) ^ (1263766531 - 1) =
          (Precompile.modPow 10 (1263766531 - 1) 1263766531 : ZMod 1263766531) :=
        zmod_pow_modPow (m := 1263766531) (a := 10) (e := 1263766531 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 10 (1263766531 - 1) 1263766531 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (10 : ZMod 1263766531) ^ ((1263766531 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((1263766531 - 1) / 2) 1263766531 (by decide) (by decide)]
      decide
    have hneq3 : (10 : ZMod 1263766531) ^ ((1263766531 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((1263766531 - 1) / 3) 1263766531 (by decide) (by decide)]
      decide
    have hneq5 : (10 : ZMod 1263766531) ^ ((1263766531 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((1263766531 - 1) / 5) 1263766531 (by decide) (by decide)]
      decide
    have hneq13 : (10 : ZMod 1263766531) ^ ((1263766531 - 1) / 13) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((1263766531 - 1) / 13) 1263766531 (by decide) (by decide)]
      decide
    have hneq911 : (10 : ZMod 1263766531) ^ ((1263766531 - 1) / 911) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((1263766531 - 1) / 911) 1263766531 (by decide) (by decide)]
      decide
    have hneq3557 : (10 : ZMod 1263766531) ^ ((1263766531 - 1) / 3557) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((1263766531 - 1) / 3557) 1263766531 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq5
    · exact hneq13
    · exact hneq911
    · exact hneq3557

theorem primeCert11465965001 : Nat.Prime 11465965001 := by
  apply lucas_of_factors (p := 11465965001) (a := 3) (xs := [2, 2, 2, 5, 5, 5, 5, 7, 327599])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert5
    · exact primeCert5
    · exact primeCert5
    · exact primeCert5
    · exact primeCert7
    · exact primeCert327599
  · calc
      (3 : ZMod 11465965001) ^ (11465965001 - 1) =
          (Precompile.modPow 3 (11465965001 - 1) 11465965001 : ZMod 11465965001) :=
        zmod_pow_modPow (m := 11465965001) (a := 3) (e := 11465965001 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (11465965001 - 1) 11465965001 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 11465965001) ^ ((11465965001 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((11465965001 - 1) / 2) 11465965001 (by decide) (by decide)]
      decide
    have hneq5 : (3 : ZMod 11465965001) ^ ((11465965001 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((11465965001 - 1) / 5) 11465965001 (by decide) (by decide)]
      decide
    have hneq7 : (3 : ZMod 11465965001) ^ ((11465965001 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((11465965001 - 1) / 7) 11465965001 (by decide) (by decide)]
      decide
    have hneq327599 : (3 : ZMod 11465965001) ^ ((11465965001 - 1) / 327599) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((11465965001 - 1) / 327599) 11465965001 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq5
    · exact hneq5
    · exact hneq5
    · exact hneq5
    · exact hneq7
    · exact hneq327599

theorem primeCert35385462869 : Nat.Prime 35385462869 := by
  apply lucas_of_factors (p := 35385462869) (a := 2) (xs := [2, 2, 7, 1263766531])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert7
    · exact primeCert1263766531
  · calc
      (2 : ZMod 35385462869) ^ (35385462869 - 1) =
          (Precompile.modPow 2 (35385462869 - 1) 35385462869 : ZMod 35385462869) :=
        zmod_pow_modPow (m := 35385462869) (a := 2) (e := 35385462869 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (35385462869 - 1) 35385462869 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 35385462869) ^ ((35385462869 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((35385462869 - 1) / 2) 35385462869 (by decide) (by decide)]
      decide
    have hneq7 : (2 : ZMod 35385462869) ^ ((35385462869 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((35385462869 - 1) / 7) 35385462869 (by decide) (by decide)]
      decide
    have hneq1263766531 : (2 : ZMod 35385462869) ^ ((35385462869 - 1) / 1263766531) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((35385462869 - 1) / 1263766531) 35385462869 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq7
    · exact hneq1263766531

theorem primeCert2480874801745591 : Nat.Prime 2480874801745591 := by
  apply lucas_of_factors (p := 2480874801745591) (a := 6) (xs := [2, 3, 3, 5, 19, 41, 35385462869])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
    · exact primeCert5
    · exact primeCert19
    · exact primeCert41
    · exact primeCert35385462869
  · calc
      (6 : ZMod 2480874801745591) ^ (2480874801745591 - 1) =
          (Precompile.modPow 6 (2480874801745591 - 1) 2480874801745591 : ZMod 2480874801745591) :=
        zmod_pow_modPow (m := 2480874801745591) (a := 6) (e := 2480874801745591 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 6 (2480874801745591 - 1) 2480874801745591 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (6 : ZMod 2480874801745591) ^ ((2480874801745591 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((2480874801745591 - 1) / 2) 2480874801745591 (by decide) (by decide)]
      decide
    have hneq3 : (6 : ZMod 2480874801745591) ^ ((2480874801745591 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((2480874801745591 - 1) / 3) 2480874801745591 (by decide) (by decide)]
      decide
    have hneq5 : (6 : ZMod 2480874801745591) ^ ((2480874801745591 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((2480874801745591 - 1) / 5) 2480874801745591 (by decide) (by decide)]
      decide
    have hneq19 : (6 : ZMod 2480874801745591) ^ ((2480874801745591 - 1) / 19) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((2480874801745591 - 1) / 19) 2480874801745591 (by decide) (by decide)]
      decide
    have hneq41 : (6 : ZMod 2480874801745591) ^ ((2480874801745591 - 1) / 41) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((2480874801745591 - 1) / 41) 2480874801745591 (by decide) (by decide)]
      decide
    have hneq35385462869 : (6 : ZMod 2480874801745591) ^ ((2480874801745591 - 1) / 35385462869) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((2480874801745591 - 1) / 35385462869) 2480874801745591 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq3
    · exact hneq5
    · exact hneq19
    · exact hneq41
    · exact hneq35385462869

theorem primeCert13427688667394608761327070753331941386769 : Nat.Prime 13427688667394608761327070753331941386769 := by
  apply lucas_of_factors (p := 13427688667394608761327070753331941386769) (a := 17) (xs := [2, 2, 2, 2, 3, 7, 11, 1853641, 4562087, 173171039, 2480874801745591])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert7
    · exact primeCert11
    · exact primeCert1853641
    · exact primeCert4562087
    · exact primeCert173171039
    · exact primeCert2480874801745591
  · calc
      (17 : ZMod 13427688667394608761327070753331941386769) ^ (13427688667394608761327070753331941386769 - 1) =
          (Precompile.modPow 17 (13427688667394608761327070753331941386769 - 1) 13427688667394608761327070753331941386769 : ZMod 13427688667394608761327070753331941386769) :=
        zmod_pow_modPow (m := 13427688667394608761327070753331941386769) (a := 17) (e := 13427688667394608761327070753331941386769 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 17 (13427688667394608761327070753331941386769 - 1) 13427688667394608761327070753331941386769 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (17 : ZMod 13427688667394608761327070753331941386769) ^ ((13427688667394608761327070753331941386769 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((13427688667394608761327070753331941386769 - 1) / 2) 13427688667394608761327070753331941386769 (by decide) (by decide)]
      decide
    have hneq3 : (17 : ZMod 13427688667394608761327070753331941386769) ^ ((13427688667394608761327070753331941386769 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((13427688667394608761327070753331941386769 - 1) / 3) 13427688667394608761327070753331941386769 (by decide) (by decide)]
      decide
    have hneq7 : (17 : ZMod 13427688667394608761327070753331941386769) ^ ((13427688667394608761327070753331941386769 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((13427688667394608761327070753331941386769 - 1) / 7) 13427688667394608761327070753331941386769 (by decide) (by decide)]
      decide
    have hneq11 : (17 : ZMod 13427688667394608761327070753331941386769) ^ ((13427688667394608761327070753331941386769 - 1) / 11) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((13427688667394608761327070753331941386769 - 1) / 11) 13427688667394608761327070753331941386769 (by decide) (by decide)]
      decide
    have hneq1853641 : (17 : ZMod 13427688667394608761327070753331941386769) ^ ((13427688667394608761327070753331941386769 - 1) / 1853641) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((13427688667394608761327070753331941386769 - 1) / 1853641) 13427688667394608761327070753331941386769 (by decide) (by decide)]
      decide
    have hneq4562087 : (17 : ZMod 13427688667394608761327070753331941386769) ^ ((13427688667394608761327070753331941386769 - 1) / 4562087) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((13427688667394608761327070753331941386769 - 1) / 4562087) 13427688667394608761327070753331941386769 (by decide) (by decide)]
      decide
    have hneq173171039 : (17 : ZMod 13427688667394608761327070753331941386769) ^ ((13427688667394608761327070753331941386769 - 1) / 173171039) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((13427688667394608761327070753331941386769 - 1) / 173171039) 13427688667394608761327070753331941386769 (by decide) (by decide)]
      decide
    have hneq2480874801745591 : (17 : ZMod 13427688667394608761327070753331941386769) ^ ((13427688667394608761327070753331941386769 - 1) / 2480874801745591) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 17 ((13427688667394608761327070753331941386769 - 1) / 2480874801745591) 13427688667394608761327070753331941386769 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq7
    · exact hneq11
    · exact hneq1853641
    · exact hneq4562087
    · exact hneq173171039
    · exact hneq2480874801745591

def bn254Factors : List Nat := [2, 3, 3, 13, 29, 67, 229, 311, 983, 11003, 405928799, 11465965001, 13427688667394608761327070753331941386769]

theorem bn254P_prime_of_certificate
    (hfermat : (3 : ZMod bn254P) ^ (bn254P - 1) = 1)
    (hprime : ∀ x ∈ bn254Factors, x.Prime)
    (hneq : ∀ x ∈ bn254Factors,
      (3 : ZMod bn254P) ^ ((bn254P - 1) / x) ≠ 1) : bn254P.Prime := by
  apply lucas_of_factors (p := bn254P) (a := 3) (xs := bn254Factors)
  · norm_num [bn254P, bn254Factors, List.prod]
  · exact hprime
  · exact hfermat
  · exact hneq

theorem bn254P_prime : Nat.Prime bn254P := by
  apply lucas_of_factors (p := bn254P) (a := 3) (xs := [2, 3, 3, 13, 29, 67, 229, 311, 983, 11003, 405928799, 11465965001, 13427688667394608761327070753331941386769])
  · norm_num [bn254P, List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
    · exact primeCert13
    · exact primeCert29
    · exact primeCert67
    · exact primeCert229
    · exact primeCert311
    · exact primeCert983
    · exact primeCert11003
    · exact primeCert405928799
    · exact primeCert11465965001
    · exact primeCert13427688667394608761327070753331941386769
  · calc
      (3 : ZMod bn254P) ^ (bn254P - 1) =
          (Precompile.modPow 3 (bn254P - 1) bn254P : ZMod bn254P) :=
        zmod_pow_modPow (m := bn254P) (a := 3) (e := bn254P - 1) (by norm_num [bn254P])
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (bn254P - 1) bn254P (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 2) bn254P (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 3) bn254P (by decide) (by decide)]
      decide
    have hneq13 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 13) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 13) bn254P (by decide) (by decide)]
      decide
    have hneq29 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 29) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 29) bn254P (by decide) (by decide)]
      decide
    have hneq67 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 67) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 67) bn254P (by decide) (by decide)]
      decide
    have hneq229 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 229) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 229) bn254P (by decide) (by decide)]
      decide
    have hneq311 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 311) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 311) bn254P (by decide) (by decide)]
      decide
    have hneq983 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 983) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 983) bn254P (by decide) (by decide)]
      decide
    have hneq11003 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 11003) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 11003) bn254P (by decide) (by decide)]
      decide
    have hneq405928799 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 405928799) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 405928799) bn254P (by decide) (by decide)]
      decide
    have hneq11465965001 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 11465965001) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 11465965001) bn254P (by decide) (by decide)]
      decide
    have hneq13427688667394608761327070753331941386769 : (3 : ZMod bn254P) ^ ((bn254P - 1) / 13427688667394608761327070753331941386769) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [bn254P])
      rw [PrimeEval.modPow_eq_eval 256 3 ((bn254P - 1) / 13427688667394608761327070753331941386769) bn254P (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq3
    · exact hneq13
    · exact hneq29
    · exact hneq67
    · exact hneq229
    · exact hneq311
    · exact hneq983
    · exact hneq11003
    · exact hneq405928799
    · exact hneq11465965001
    · exact hneq13427688667394608761327070753331941386769


def secpP : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

theorem primeCert53 : Nat.Prime 53 := by
  apply lucas_of_factors (p := 53) (a := 2) (xs := [2, 2, 13])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert13
  · calc
      (2 : ZMod 53) ^ (53 - 1) =
          (Precompile.modPow 2 (53 - 1) 53 : ZMod 53) :=
        zmod_pow_modPow (m := 53) (a := 2) (e := 53 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (53 - 1) 53 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 53) ^ ((53 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((53 - 1) / 2) 53 (by decide) (by decide)]
      decide
    have hneq13 : (2 : ZMod 53) ^ ((53 - 1) / 13) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((53 - 1) / 13) 53 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq13

theorem primeCert83 : Nat.Prime 83 := by
  apply lucas_of_factors (p := 83) (a := 2) (xs := [2, 41])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact primeCert2
    · exact primeCert41
  · calc
      (2 : ZMod 83) ^ (83 - 1) =
          (Precompile.modPow 2 (83 - 1) 83 : ZMod 83) :=
        zmod_pow_modPow (m := 83) (a := 2) (e := 83 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (83 - 1) 83 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 83) ^ ((83 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((83 - 1) / 2) 83 (by decide) (by decide)]
      decide
    have hneq41 : (2 : ZMod 83) ^ ((83 - 1) / 41) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((83 - 1) / 41) 83 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact hneq2
    · exact hneq41

theorem primeCert97 : Nat.Prime 97 := by
  apply lucas_of_factors (p := 97) (a := 5) (xs := [2, 2, 2, 2, 2, 3])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
  · calc
      (5 : ZMod 97) ^ (97 - 1) =
          (Precompile.modPow 5 (97 - 1) 97 : ZMod 97) :=
        zmod_pow_modPow (m := 97) (a := 5) (e := 97 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 5 (97 - 1) 97 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (5 : ZMod 97) ^ ((97 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((97 - 1) / 2) 97 (by decide) (by decide)]
      decide
    have hneq3 : (5 : ZMod 97) ^ ((97 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((97 - 1) / 3) 97 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq3

theorem primeCert101 : Nat.Prime 101 := by
  apply lucas_of_factors (p := 101) (a := 2) (xs := [2, 2, 5, 5])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert5
    · exact primeCert5
  · calc
      (2 : ZMod 101) ^ (101 - 1) =
          (Precompile.modPow 2 (101 - 1) 101 : ZMod 101) :=
        zmod_pow_modPow (m := 101) (a := 2) (e := 101 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (101 - 1) 101 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 101) ^ ((101 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((101 - 1) / 2) 101 (by decide) (by decide)]
      decide
    have hneq5 : (2 : ZMod 101) ^ ((101 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((101 - 1) / 5) 101 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq5
    · exact hneq5

theorem primeCert103 : Nat.Prime 103 := by
  apply lucas_of_factors (p := 103) (a := 5) (xs := [2, 3, 17])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert17
  · calc
      (5 : ZMod 103) ^ (103 - 1) =
          (Precompile.modPow 5 (103 - 1) 103 : ZMod 103) :=
        zmod_pow_modPow (m := 103) (a := 5) (e := 103 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 5 (103 - 1) 103 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (5 : ZMod 103) ^ ((103 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((103 - 1) / 2) 103 (by decide) (by decide)]
      decide
    have hneq3 : (5 : ZMod 103) ^ ((103 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((103 - 1) / 3) 103 (by decide) (by decide)]
      decide
    have hneq17 : (5 : ZMod 103) ^ ((103 - 1) / 17) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((103 - 1) / 17) 103 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq17

theorem primeCert131 : Nat.Prime 131 := by
  apply lucas_of_factors (p := 131) (a := 2) (xs := [2, 5, 13])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert5
    · exact primeCert13
  · calc
      (2 : ZMod 131) ^ (131 - 1) =
          (Precompile.modPow 2 (131 - 1) 131 : ZMod 131) :=
        zmod_pow_modPow (m := 131) (a := 2) (e := 131 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (131 - 1) 131 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 131) ^ ((131 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((131 - 1) / 2) 131 (by decide) (by decide)]
      decide
    have hneq5 : (2 : ZMod 131) ^ ((131 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((131 - 1) / 5) 131 (by decide) (by decide)]
      decide
    have hneq13 : (2 : ZMod 131) ^ ((131 - 1) / 13) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((131 - 1) / 13) 131 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq5
    · exact hneq13

theorem primeCert239 : Nat.Prime 239 := by
  apply lucas_of_factors (p := 239) (a := 7) (xs := [2, 7, 17])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert7
    · exact primeCert17
  · calc
      (7 : ZMod 239) ^ (239 - 1) =
          (Precompile.modPow 7 (239 - 1) 239 : ZMod 239) :=
        zmod_pow_modPow (m := 239) (a := 7) (e := 239 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 7 (239 - 1) 239 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (7 : ZMod 239) ^ ((239 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 7 ((239 - 1) / 2) 239 (by decide) (by decide)]
      decide
    have hneq7 : (7 : ZMod 239) ^ ((239 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 7 ((239 - 1) / 7) 239 (by decide) (by decide)]
      decide
    have hneq17 : (7 : ZMod 239) ^ ((239 - 1) / 17) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 7 ((239 - 1) / 17) 239 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq7
    · exact hneq17

theorem primeCert419 : Nat.Prime 419 := by
  apply lucas_of_factors (p := 419) (a := 2) (xs := [2, 11, 19])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert11
    · exact primeCert19
  · calc
      (2 : ZMod 419) ^ (419 - 1) =
          (Precompile.modPow 2 (419 - 1) 419 : ZMod 419) :=
        zmod_pow_modPow (m := 419) (a := 2) (e := 419 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (419 - 1) 419 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 419) ^ ((419 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((419 - 1) / 2) 419 (by decide) (by decide)]
      decide
    have hneq11 : (2 : ZMod 419) ^ ((419 - 1) / 11) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((419 - 1) / 11) 419 (by decide) (by decide)]
      decide
    have hneq19 : (2 : ZMod 419) ^ ((419 - 1) / 19) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((419 - 1) / 19) 419 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq11
    · exact hneq19

theorem primeCert443 : Nat.Prime 443 := by
  apply lucas_of_factors (p := 443) (a := 2) (xs := [2, 13, 17])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert13
    · exact primeCert17
  · calc
      (2 : ZMod 443) ^ (443 - 1) =
          (Precompile.modPow 2 (443 - 1) 443 : ZMod 443) :=
        zmod_pow_modPow (m := 443) (a := 2) (e := 443 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (443 - 1) 443 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 443) ^ ((443 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((443 - 1) / 2) 443 (by decide) (by decide)]
      decide
    have hneq13 : (2 : ZMod 443) ^ ((443 - 1) / 13) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((443 - 1) / 13) 443 (by decide) (by decide)]
      decide
    have hneq17 : (2 : ZMod 443) ^ ((443 - 1) / 17) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((443 - 1) / 17) 443 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq13
    · exact hneq17

theorem primeCert887 : Nat.Prime 887 := by
  apply lucas_of_factors (p := 887) (a := 5) (xs := [2, 443])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact primeCert2
    · exact primeCert443
  · calc
      (5 : ZMod 887) ^ (887 - 1) =
          (Precompile.modPow 5 (887 - 1) 887 : ZMod 887) :=
        zmod_pow_modPow (m := 887) (a := 5) (e := 887 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 5 (887 - 1) 887 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (5 : ZMod 887) ^ ((887 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((887 - 1) / 2) 887 (by decide) (by decide)]
      decide
    have hneq443 : (5 : ZMod 887) ^ ((887 - 1) / 443) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((887 - 1) / 443) 887 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl)
    · exact hneq2
    · exact hneq443

theorem primeCert971 : Nat.Prime 971 := by
  apply lucas_of_factors (p := 971) (a := 6) (xs := [2, 5, 97])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert5
    · exact primeCert97
  · calc
      (6 : ZMod 971) ^ (971 - 1) =
          (Precompile.modPow 6 (971 - 1) 971 : ZMod 971) :=
        zmod_pow_modPow (m := 971) (a := 6) (e := 971 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 6 (971 - 1) 971 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (6 : ZMod 971) ^ ((971 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((971 - 1) / 2) 971 (by decide) (by decide)]
      decide
    have hneq5 : (6 : ZMod 971) ^ ((971 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((971 - 1) / 5) 971 (by decide) (by decide)]
      decide
    have hneq97 : (6 : ZMod 971) ^ ((971 - 1) / 97) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((971 - 1) / 97) 971 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq5
    · exact hneq97

theorem primeCert1373 : Nat.Prime 1373 := by
  apply lucas_of_factors (p := 1373) (a := 2) (xs := [2, 2, 7, 7, 7])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert7
    · exact primeCert7
    · exact primeCert7
  · calc
      (2 : ZMod 1373) ^ (1373 - 1) =
          (Precompile.modPow 2 (1373 - 1) 1373 : ZMod 1373) :=
        zmod_pow_modPow (m := 1373) (a := 2) (e := 1373 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (1373 - 1) 1373 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 1373) ^ ((1373 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((1373 - 1) / 2) 1373 (by decide) (by decide)]
      decide
    have hneq7 : (2 : ZMod 1373) ^ ((1373 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((1373 - 1) / 7) 1373 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq7
    · exact hneq7
    · exact hneq7

theorem primeCert1627 : Nat.Prime 1627 := by
  apply lucas_of_factors (p := 1627) (a := 3) (xs := [2, 3, 271])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert271
  · calc
      (3 : ZMod 1627) ^ (1627 - 1) =
          (Precompile.modPow 3 (1627 - 1) 1627 : ZMod 1627) :=
        zmod_pow_modPow (m := 1627) (a := 3) (e := 1627 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (1627 - 1) 1627 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 1627) ^ ((1627 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((1627 - 1) / 2) 1627 (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod 1627) ^ ((1627 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((1627 - 1) / 3) 1627 (by decide) (by decide)]
      decide
    have hneq271 : (3 : ZMod 1627) ^ ((1627 - 1) / 271) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((1627 - 1) / 271) 1627 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq271

theorem primeCert2621 : Nat.Prime 2621 := by
  apply lucas_of_factors (p := 2621) (a := 2) (xs := [2, 2, 5, 131])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert5
    · exact primeCert131
  · calc
      (2 : ZMod 2621) ^ (2621 - 1) =
          (Precompile.modPow 2 (2621 - 1) 2621 : ZMod 2621) :=
        zmod_pow_modPow (m := 2621) (a := 2) (e := 2621 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (2621 - 1) 2621 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 2621) ^ ((2621 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((2621 - 1) / 2) 2621 (by decide) (by decide)]
      decide
    have hneq5 : (2 : ZMod 2621) ^ ((2621 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((2621 - 1) / 5) 2621 (by decide) (by decide)]
      decide
    have hneq131 : (2 : ZMod 2621) ^ ((2621 - 1) / 131) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((2621 - 1) / 131) 2621 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq5
    · exact hneq131

theorem primeCert2657 : Nat.Prime 2657 := by
  apply lucas_of_factors (p := 2657) (a := 3) (xs := [2, 2, 2, 2, 2, 83])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert83
  · calc
      (3 : ZMod 2657) ^ (2657 - 1) =
          (Precompile.modPow 3 (2657 - 1) 2657 : ZMod 2657) :=
        zmod_pow_modPow (m := 2657) (a := 3) (e := 2657 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (2657 - 1) 2657 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 2657) ^ ((2657 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((2657 - 1) / 2) 2657 (by decide) (by decide)]
      decide
    have hneq83 : (3 : ZMod 2657) ^ ((2657 - 1) / 83) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((2657 - 1) / 83) 2657 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq83

theorem primeCert4423 : Nat.Prime 4423 := by
  apply lucas_of_factors (p := 4423) (a := 3) (xs := [2, 3, 11, 67])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert11
    · exact primeCert67
  · calc
      (3 : ZMod 4423) ^ (4423 - 1) =
          (Precompile.modPow 3 (4423 - 1) 4423 : ZMod 4423) :=
        zmod_pow_modPow (m := 4423) (a := 3) (e := 4423 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (4423 - 1) 4423 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 4423) ^ ((4423 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((4423 - 1) / 2) 4423 (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod 4423) ^ ((4423 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((4423 - 1) / 3) 4423 (by decide) (by decide)]
      decide
    have hneq11 : (3 : ZMod 4423) ^ ((4423 - 1) / 11) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((4423 - 1) / 11) 4423 (by decide) (by decide)]
      decide
    have hneq67 : (3 : ZMod 4423) ^ ((4423 - 1) / 67) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((4423 - 1) / 67) 4423 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq11
    · exact hneq67

theorem primeCert5323 : Nat.Prime 5323 := by
  apply lucas_of_factors (p := 5323) (a := 5) (xs := [2, 3, 887])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert887
  · calc
      (5 : ZMod 5323) ^ (5323 - 1) =
          (Precompile.modPow 5 (5323 - 1) 5323 : ZMod 5323) :=
        zmod_pow_modPow (m := 5323) (a := 5) (e := 5323 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 5 (5323 - 1) 5323 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (5 : ZMod 5323) ^ ((5323 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((5323 - 1) / 2) 5323 (by decide) (by decide)]
      decide
    have hneq3 : (5 : ZMod 5323) ^ ((5323 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((5323 - 1) / 3) 5323 (by decide) (by decide)]
      decide
    have hneq887 : (5 : ZMod 5323) ^ ((5323 - 1) / 887) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((5323 - 1) / 887) 5323 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq887

theorem primeCert7723 : Nat.Prime 7723 := by
  apply lucas_of_factors (p := 7723) (a := 3) (xs := [2, 3, 3, 3, 11, 13])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert3
    · exact primeCert3
    · exact primeCert11
    · exact primeCert13
  · calc
      (3 : ZMod 7723) ^ (7723 - 1) =
          (Precompile.modPow 3 (7723 - 1) 7723 : ZMod 7723) :=
        zmod_pow_modPow (m := 7723) (a := 3) (e := 7723 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (7723 - 1) 7723 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 7723) ^ ((7723 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((7723 - 1) / 2) 7723 (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod 7723) ^ ((7723 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((7723 - 1) / 3) 7723 (by decide) (by decide)]
      decide
    have hneq11 : (3 : ZMod 7723) ^ ((7723 - 1) / 11) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((7723 - 1) / 11) 7723 (by decide) (by decide)]
      decide
    have hneq13 : (3 : ZMod 7723) ^ ((7723 - 1) / 13) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((7723 - 1) / 13) 7723 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq3
    · exact hneq3
    · exact hneq11
    · exact hneq13

theorem primeCert13441 : Nat.Prime 13441 := by
  apply lucas_of_factors (p := 13441) (a := 11) (xs := [2, 2, 2, 2, 2, 2, 2, 3, 5, 7])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert5
    · exact primeCert7
  · calc
      (11 : ZMod 13441) ^ (13441 - 1) =
          (Precompile.modPow 11 (13441 - 1) 13441 : ZMod 13441) :=
        zmod_pow_modPow (m := 13441) (a := 11) (e := 13441 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 11 (13441 - 1) 13441 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (11 : ZMod 13441) ^ ((13441 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 11 ((13441 - 1) / 2) 13441 (by decide) (by decide)]
      decide
    have hneq3 : (11 : ZMod 13441) ^ ((13441 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 11 ((13441 - 1) / 3) 13441 (by decide) (by decide)]
      decide
    have hneq5 : (11 : ZMod 13441) ^ ((13441 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 11 ((13441 - 1) / 5) 13441 (by decide) (by decide)]
      decide
    have hneq7 : (11 : ZMod 13441) ^ ((13441 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 11 ((13441 - 1) / 7) 13441 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq5
    · exact hneq7

theorem primeCert20113 : Nat.Prime 20113 := by
  apply lucas_of_factors (p := 20113) (a := 10) (xs := [2, 2, 2, 2, 3, 419])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert419
  · calc
      (10 : ZMod 20113) ^ (20113 - 1) =
          (Precompile.modPow 10 (20113 - 1) 20113 : ZMod 20113) :=
        zmod_pow_modPow (m := 20113) (a := 10) (e := 20113 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 10 (20113 - 1) 20113 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (10 : ZMod 20113) ^ ((20113 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((20113 - 1) / 2) 20113 (by decide) (by decide)]
      decide
    have hneq3 : (10 : ZMod 20113) ^ ((20113 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((20113 - 1) / 3) 20113 (by decide) (by decide)]
      decide
    have hneq419 : (10 : ZMod 20113) ^ ((20113 - 1) / 419) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((20113 - 1) / 419) 20113 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq419

theorem primeCert24809 : Nat.Prime 24809 := by
  apply lucas_of_factors (p := 24809) (a := 6) (xs := [2, 2, 2, 7, 443])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert7
    · exact primeCert443
  · calc
      (6 : ZMod 24809) ^ (24809 - 1) =
          (Precompile.modPow 6 (24809 - 1) 24809 : ZMod 24809) :=
        zmod_pow_modPow (m := 24809) (a := 6) (e := 24809 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 6 (24809 - 1) 24809 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (6 : ZMod 24809) ^ ((24809 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((24809 - 1) / 2) 24809 (by decide) (by decide)]
      decide
    have hneq7 : (6 : ZMod 24809) ^ ((24809 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((24809 - 1) / 7) 24809 (by decide) (by decide)]
      decide
    have hneq443 : (6 : ZMod 24809) ^ ((24809 - 1) / 443) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((24809 - 1) / 443) 24809 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq7
    · exact hneq443

theorem primeCert41201 : Nat.Prime 41201 := by
  apply lucas_of_factors (p := 41201) (a := 3) (xs := [2, 2, 2, 2, 5, 5, 103])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert5
    · exact primeCert5
    · exact primeCert103
  · calc
      (3 : ZMod 41201) ^ (41201 - 1) =
          (Precompile.modPow 3 (41201 - 1) 41201 : ZMod 41201) :=
        zmod_pow_modPow (m := 41201) (a := 3) (e := 41201 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (41201 - 1) 41201 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 41201) ^ ((41201 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((41201 - 1) / 2) 41201 (by decide) (by decide)]
      decide
    have hneq5 : (3 : ZMod 41201) ^ ((41201 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((41201 - 1) / 5) 41201 (by decide) (by decide)]
      decide
    have hneq103 : (3 : ZMod 41201) ^ ((41201 - 1) / 103) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((41201 - 1) / 103) 41201 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq5
    · exact hneq5
    · exact hneq103

theorem primeCert96557 : Nat.Prime 96557 := by
  apply lucas_of_factors (p := 96557) (a := 2) (xs := [2, 2, 101, 239])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert101
    · exact primeCert239
  · calc
      (2 : ZMod 96557) ^ (96557 - 1) =
          (Precompile.modPow 2 (96557 - 1) 96557 : ZMod 96557) :=
        zmod_pow_modPow (m := 96557) (a := 2) (e := 96557 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 2 (96557 - 1) 96557 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (2 : ZMod 96557) ^ ((96557 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((96557 - 1) / 2) 96557 (by decide) (by decide)]
      decide
    have hneq101 : (2 : ZMod 96557) ^ ((96557 - 1) / 101) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((96557 - 1) / 101) 96557 (by decide) (by decide)]
      decide
    have hneq239 : (2 : ZMod 96557) ^ ((96557 - 1) / 239) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 2 ((96557 - 1) / 239) 96557 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq101
    · exact hneq239

theorem primeCert1206781 : Nat.Prime 1206781 := by
  apply lucas_of_factors (p := 1206781) (a := 10) (xs := [2, 2, 3, 5, 20113])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert5
    · exact primeCert20113
  · calc
      (10 : ZMod 1206781) ^ (1206781 - 1) =
          (Precompile.modPow 10 (1206781 - 1) 1206781 : ZMod 1206781) :=
        zmod_pow_modPow (m := 1206781) (a := 10) (e := 1206781 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 10 (1206781 - 1) 1206781 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (10 : ZMod 1206781) ^ ((1206781 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((1206781 - 1) / 2) 1206781 (by decide) (by decide)]
      decide
    have hneq3 : (10 : ZMod 1206781) ^ ((1206781 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((1206781 - 1) / 3) 1206781 (by decide) (by decide)]
      decide
    have hneq5 : (10 : ZMod 1206781) ^ ((1206781 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((1206781 - 1) / 5) 1206781 (by decide) (by decide)]
      decide
    have hneq20113 : (10 : ZMod 1206781) ^ ((1206781 - 1) / 20113) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((1206781 - 1) / 20113) 1206781 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq5
    · exact hneq20113

theorem primeCert7240687 : Nat.Prime 7240687 := by
  apply lucas_of_factors (p := 7240687) (a := 3) (xs := [2, 3, 1206781])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert1206781
  · calc
      (3 : ZMod 7240687) ^ (7240687 - 1) =
          (Precompile.modPow 3 (7240687 - 1) 7240687 : ZMod 7240687) :=
        zmod_pow_modPow (m := 7240687) (a := 3) (e := 7240687 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (7240687 - 1) 7240687 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 7240687) ^ ((7240687 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((7240687 - 1) / 2) 7240687 (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod 7240687) ^ ((7240687 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((7240687 - 1) / 3) 7240687 (by decide) (by decide)]
      decide
    have hneq1206781 : (3 : ZMod 7240687) ^ ((7240687 - 1) / 1206781) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((7240687 - 1) / 1206781) 7240687 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq1206781

theorem primeCert13331831 : Nat.Prime 13331831 := by
  apply lucas_of_factors (p := 13331831) (a := 13) (xs := [2, 5, 971, 1373])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert5
    · exact primeCert971
    · exact primeCert1373
  · calc
      (13 : ZMod 13331831) ^ (13331831 - 1) =
          (Precompile.modPow 13 (13331831 - 1) 13331831 : ZMod 13331831) :=
        zmod_pow_modPow (m := 13331831) (a := 13) (e := 13331831 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 13 (13331831 - 1) 13331831 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (13 : ZMod 13331831) ^ ((13331831 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 13 ((13331831 - 1) / 2) 13331831 (by decide) (by decide)]
      decide
    have hneq5 : (13 : ZMod 13331831) ^ ((13331831 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 13 ((13331831 - 1) / 5) 13331831 (by decide) (by decide)]
      decide
    have hneq971 : (13 : ZMod 13331831) ^ ((13331831 - 1) / 971) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 13 ((13331831 - 1) / 971) 13331831 (by decide) (by decide)]
      decide
    have hneq1373 : (13 : ZMod 13331831) ^ ((13331831 - 1) / 1373) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 13 ((13331831 - 1) / 1373) 13331831 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq5
    · exact hneq971
    · exact hneq1373

theorem primeCert107590001 : Nat.Prime 107590001 := by
  apply lucas_of_factors (p := 107590001) (a := 3) (xs := [2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert5
    · exact primeCert5
    · exact primeCert5
    · exact primeCert5
    · exact primeCert7
    · exact primeCert29
    · exact primeCert53
  · calc
      (3 : ZMod 107590001) ^ (107590001 - 1) =
          (Precompile.modPow 3 (107590001 - 1) 107590001 : ZMod 107590001) :=
        zmod_pow_modPow (m := 107590001) (a := 3) (e := 107590001 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (107590001 - 1) 107590001 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 107590001) ^ ((107590001 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((107590001 - 1) / 2) 107590001 (by decide) (by decide)]
      decide
    have hneq5 : (3 : ZMod 107590001) ^ ((107590001 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((107590001 - 1) / 5) 107590001 (by decide) (by decide)]
      decide
    have hneq7 : (3 : ZMod 107590001) ^ ((107590001 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((107590001 - 1) / 7) 107590001 (by decide) (by decide)]
      decide
    have hneq29 : (3 : ZMod 107590001) ^ ((107590001 - 1) / 29) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((107590001 - 1) / 29) 107590001 (by decide) (by decide)]
      decide
    have hneq53 : (3 : ZMod 107590001) ^ ((107590001 - 1) / 53) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((107590001 - 1) / 53) 107590001 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq5
    · exact hneq5
    · exact hneq5
    · exact hneq5
    · exact hneq7
    · exact hneq29
    · exact hneq53

theorem primeCert173378833005251801 : Nat.Prime 173378833005251801 := by
  apply lucas_of_factors (p := 173378833005251801) (a := 6) (xs := [2, 2, 2, 5, 5, 2621, 24809, 13331831])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert5
    · exact primeCert5
    · exact primeCert2621
    · exact primeCert24809
    · exact primeCert13331831
  · calc
      (6 : ZMod 173378833005251801) ^ (173378833005251801 - 1) =
          (Precompile.modPow 6 (173378833005251801 - 1) 173378833005251801 : ZMod 173378833005251801) :=
        zmod_pow_modPow (m := 173378833005251801) (a := 6) (e := 173378833005251801 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 6 (173378833005251801 - 1) 173378833005251801 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((173378833005251801 - 1) / 2) 173378833005251801 (by decide) (by decide)]
      decide
    have hneq5 : (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((173378833005251801 - 1) / 5) 173378833005251801 (by decide) (by decide)]
      decide
    have hneq2621 : (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 2621) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((173378833005251801 - 1) / 2621) 173378833005251801 (by decide) (by decide)]
      decide
    have hneq24809 : (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 24809) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((173378833005251801 - 1) / 24809) 173378833005251801 (by decide) (by decide)]
      decide
    have hneq13331831 : (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 13331831) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((173378833005251801 - 1) / 13331831) 173378833005251801 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq5
    · exact hneq5
    · exact hneq2621
    · exact hneq24809
    · exact hneq13331831

theorem primeCert22149492674086928081353 : Nat.Prime 22149492674086928081353 := by
  apply lucas_of_factors (p := 22149492674086928081353) (a := 5) (xs := [2, 2, 2, 3, 5323, 173378833005251801])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert3
    · exact primeCert5323
    · exact primeCert173378833005251801
  · calc
      (5 : ZMod 22149492674086928081353) ^ (22149492674086928081353 - 1) =
          (Precompile.modPow 5 (22149492674086928081353 - 1) 22149492674086928081353 : ZMod 22149492674086928081353) :=
        zmod_pow_modPow (m := 22149492674086928081353) (a := 5) (e := 22149492674086928081353 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 5 (22149492674086928081353 - 1) 22149492674086928081353 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((22149492674086928081353 - 1) / 2) 22149492674086928081353 (by decide) (by decide)]
      decide
    have hneq3 : (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((22149492674086928081353 - 1) / 3) 22149492674086928081353 (by decide) (by decide)]
      decide
    have hneq5323 : (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / 5323) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((22149492674086928081353 - 1) / 5323) 22149492674086928081353 (by decide) (by decide)]
      decide
    have hneq173378833005251801 : (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / 173378833005251801) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 5 ((22149492674086928081353 - 1) / 173378833005251801) 22149492674086928081353 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq3
    · exact hneq5323
    · exact hneq173378833005251801

theorem primeCert132896956044521568488119 : Nat.Prime 132896956044521568488119 := by
  apply lucas_of_factors (p := 132896956044521568488119) (a := 6) (xs := [2, 3, 22149492674086928081353])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert22149492674086928081353
  · calc
      (6 : ZMod 132896956044521568488119) ^ (132896956044521568488119 - 1) =
          (Precompile.modPow 6 (132896956044521568488119 - 1) 132896956044521568488119 : ZMod 132896956044521568488119) :=
        zmod_pow_modPow (m := 132896956044521568488119) (a := 6) (e := 132896956044521568488119 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 6 (132896956044521568488119 - 1) 132896956044521568488119 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (6 : ZMod 132896956044521568488119) ^ ((132896956044521568488119 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((132896956044521568488119 - 1) / 2) 132896956044521568488119 (by decide) (by decide)]
      decide
    have hneq3 : (6 : ZMod 132896956044521568488119) ^ ((132896956044521568488119 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((132896956044521568488119 - 1) / 3) 132896956044521568488119 (by decide) (by decide)]
      decide
    have hneq22149492674086928081353 : (6 : ZMod 132896956044521568488119) ^ ((132896956044521568488119 - 1) / 22149492674086928081353) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 6 ((132896956044521568488119 - 1) / 22149492674086928081353) 132896956044521568488119 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq22149492674086928081353

theorem primeCert255515944373312847190720520512484175977 : Nat.Prime 255515944373312847190720520512484175977 := by
  apply lucas_of_factors (p := 255515944373312847190720520512484175977) (a := 3) (xs := [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 41201, 96557, 7240687, 107590001])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert2
    · exact primeCert2
    · exact primeCert7
    · exact primeCert7
    · exact primeCert11
    · exact primeCert1627
    · exact primeCert2657
    · exact primeCert4423
    · exact primeCert41201
    · exact primeCert96557
    · exact primeCert7240687
    · exact primeCert107590001
  · calc
      (3 : ZMod 255515944373312847190720520512484175977) ^ (255515944373312847190720520512484175977 - 1) =
          (Precompile.modPow 3 (255515944373312847190720520512484175977 - 1) 255515944373312847190720520512484175977 : ZMod 255515944373312847190720520512484175977) :=
        zmod_pow_modPow (m := 255515944373312847190720520512484175977) (a := 3) (e := 255515944373312847190720520512484175977 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (255515944373312847190720520512484175977 - 1) 255515944373312847190720520512484175977 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((255515944373312847190720520512484175977 - 1) / 2) 255515944373312847190720520512484175977 (by decide) (by decide)]
      decide
    have hneq7 : (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((255515944373312847190720520512484175977 - 1) / 7) 255515944373312847190720520512484175977 (by decide) (by decide)]
      decide
    have hneq11 : (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 11) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((255515944373312847190720520512484175977 - 1) / 11) 255515944373312847190720520512484175977 (by decide) (by decide)]
      decide
    have hneq1627 : (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 1627) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((255515944373312847190720520512484175977 - 1) / 1627) 255515944373312847190720520512484175977 (by decide) (by decide)]
      decide
    have hneq2657 : (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 2657) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((255515944373312847190720520512484175977 - 1) / 2657) 255515944373312847190720520512484175977 (by decide) (by decide)]
      decide
    have hneq4423 : (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 4423) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((255515944373312847190720520512484175977 - 1) / 4423) 255515944373312847190720520512484175977 (by decide) (by decide)]
      decide
    have hneq41201 : (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 41201) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((255515944373312847190720520512484175977 - 1) / 41201) 255515944373312847190720520512484175977 (by decide) (by decide)]
      decide
    have hneq96557 : (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 96557) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((255515944373312847190720520512484175977 - 1) / 96557) 255515944373312847190720520512484175977 (by decide) (by decide)]
      decide
    have hneq7240687 : (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 7240687) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((255515944373312847190720520512484175977 - 1) / 7240687) 255515944373312847190720520512484175977 (by decide) (by decide)]
      decide
    have hneq107590001 : (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 107590001) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 3 ((255515944373312847190720520512484175977 - 1) / 107590001) 255515944373312847190720520512484175977 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq2
    · exact hneq2
    · exact hneq7
    · exact hneq7
    · exact hneq11
    · exact hneq1627
    · exact hneq2657
    · exact hneq4423
    · exact hneq41201
    · exact hneq96557
    · exact hneq7240687
    · exact hneq107590001

theorem primeCert205115282021455665897114700593932402728804164701536103180137503955397371 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  apply lucas_of_factors (p := 205115282021455665897114700593932402728804164701536103180137503955397371) (a := 10) (xs := [2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119, 255515944373312847190720520512484175977])
  · norm_num [List.prod]
  ·
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert5
    · exact primeCert29
    · exact primeCert29
    · exact primeCert31
    · exact primeCert7723
    · exact primeCert132896956044521568488119
    · exact primeCert255515944373312847190720520512484175977
  · calc
      (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ (205115282021455665897114700593932402728804164701536103180137503955397371 - 1) =
          (Precompile.modPow 10 (205115282021455665897114700593932402728804164701536103180137503955397371 - 1) 205115282021455665897114700593932402728804164701536103180137503955397371 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) :=
        zmod_pow_modPow (m := 205115282021455665897114700593932402728804164701536103180137503955397371) (a := 10) (e := 205115282021455665897114700593932402728804164701536103180137503955397371 - 1) (by norm_num)
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 10 (205115282021455665897114700593932402728804164701536103180137503955397371 - 1) 205115282021455665897114700593932402728804164701536103180137503955397371 (by decide) (by decide)]
        decide
  ·
    have hneq2 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 2) 205115282021455665897114700593932402728804164701536103180137503955397371 (by decide) (by decide)]
      decide
    have hneq3 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 3) 205115282021455665897114700593932402728804164701536103180137503955397371 (by decide) (by decide)]
      decide
    have hneq5 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 5) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 5) 205115282021455665897114700593932402728804164701536103180137503955397371 (by decide) (by decide)]
      decide
    have hneq29 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 29) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 29) 205115282021455665897114700593932402728804164701536103180137503955397371 (by decide) (by decide)]
      decide
    have hneq31 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 31) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 31) 205115282021455665897114700593932402728804164701536103180137503955397371 (by decide) (by decide)]
      decide
    have hneq7723 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 7723) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 7723) 205115282021455665897114700593932402728804164701536103180137503955397371 (by decide) (by decide)]
      decide
    have hneq132896956044521568488119 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 132896956044521568488119) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 132896956044521568488119) 205115282021455665897114700593932402728804164701536103180137503955397371 (by decide) (by decide)]
      decide
    have hneq255515944373312847190720520512484175977 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 255515944373312847190720520512484175977) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num)
      rw [PrimeEval.modPow_eq_eval 256 10 ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 255515944373312847190720520512484175977) 205115282021455665897114700593932402728804164701536103180137503955397371 (by decide) (by decide)]
      decide
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq5
    · exact hneq29
    · exact hneq29
    · exact hneq31
    · exact hneq7723
    · exact hneq132896956044521568488119
    · exact hneq255515944373312847190720520512484175977

def secpFactors : List Nat := [2, 3, 7, 13441, 205115282021455665897114700593932402728804164701536103180137503955397371]

theorem secpP_prime_of_certificate
    (hfermat : (3 : ZMod secpP) ^ (secpP - 1) = 1)
    (hprime : ∀ x ∈ secpFactors, x.Prime)
    (hneq : ∀ x ∈ secpFactors,
      (3 : ZMod secpP) ^ ((secpP - 1) / x) ≠ 1) : secpP.Prime := by
  apply lucas_of_factors (p := secpP) (a := 3) (xs := secpFactors)
  · norm_num [secpP, secpFactors, List.prod]
  · exact hprime
  · exact hfermat
  · exact hneq

theorem secpP_prime : secpP.Prime := by
  apply secpP_prime_of_certificate
  · calc
      (3 : ZMod secpP) ^ (secpP - 1) =
          (Precompile.modPow 3 (secpP - 1) secpP : ZMod secpP) :=
        zmod_pow_modPow (m := secpP) (a := 3) (e := secpP - 1) (by norm_num [secpP])
      _ = 1 := by
        rw [PrimeEval.modPow_eq_eval 256 3 (secpP - 1) secpP (by decide) (by decide)]
        decide
  ·
    intro x hx
    simp only [secpFactors, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact primeCert2
    · exact primeCert3
    · exact primeCert7
    · exact primeCert13441
    · exact primeCert205115282021455665897114700593932402728804164701536103180137503955397371
  ·
    have hneq2 : (3 : ZMod secpP) ^ ((secpP - 1) / 2) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [secpP])
      rw [PrimeEval.modPow_eq_eval 256 3 ((secpP - 1) / 2) secpP (by decide) (by decide)]
      decide
    have hneq3 : (3 : ZMod secpP) ^ ((secpP - 1) / 3) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [secpP])
      rw [PrimeEval.modPow_eq_eval 256 3 ((secpP - 1) / 3) secpP (by decide) (by decide)]
      decide
    have hneq7 : (3 : ZMod secpP) ^ ((secpP - 1) / 7) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [secpP])
      rw [PrimeEval.modPow_eq_eval 256 3 ((secpP - 1) / 7) secpP (by decide) (by decide)]
      decide
    have hneq13441 : (3 : ZMod secpP) ^ ((secpP - 1) / 13441) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [secpP])
      rw [PrimeEval.modPow_eq_eval 256 3 ((secpP - 1) / 13441) secpP (by decide) (by decide)]
      decide
    have hneq205115282021455665897114700593932402728804164701536103180137503955397371 : (3 : ZMod secpP) ^ ((secpP - 1) / 205115282021455665897114700593932402728804164701536103180137503955397371) ≠ 1 := by
      apply zmod_pow_ne_of_modPow_ne (by norm_num [secpP])
      rw [PrimeEval.modPow_eq_eval 256 3 ((secpP - 1) / 205115282021455665897114700593932402728804164701536103180137503955397371) secpP (by decide) (by decide)]
      decide
    intro x hx
    simp only [secpFactors, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact hneq2
    · exact hneq3
    · exact hneq7
    · exact hneq13441
    · exact hneq205115282021455665897114700593932402728804164701536103180137503955397371

theorem secpPrime : secpP.Prime := secpP_prime
end Challenge.Modexp.Submission.Proofs.PrimeCertificates
