import Challenge.Modexp.Submission.Proofs.Limbs
import Mathlib.Tactic

set_option warningAsError true

/-!
# The value-level specification of the `addMod` procedure

The Asm program's `addMod` procedure takes three equally-sized little-endian
limb lists — `xs` (destination), `ys` (source), `ms` (modulus), every digit
below `radix` — and computes the modular sum in two passes followed by a
selection:

* pass 1: `addDigitLists xs ys 0`, giving wrapped sum limbs plus a carry bit;
* pass 2: `subDigitLists sumLimbs ms 0`, giving a conditional-subtraction
  candidate plus a borrow bit;
* the result is the candidate when the final carry was `1` or the subtraction
  did not borrow, and the wrapped sum limbs otherwise.

`addModResult_value` proves the selected list represents exactly
`(X + Y) % M`; `doubleMod_value` is the `src = dst` (doubling) corollary.
This file is pure list/Nat arithmetic — no memory and no machine state.
-/

namespace Challenge.Modexp.Submission.Proof.AddModMath

open Challenge.Modexp.Submission.Proofs.Limbs

/-! ## A missing length lemma for `subDigitLists` -/

theorem length_subDigitLists_left {xs ys : List Nat} {borrow : Nat}
    (hlength : xs.length = ys.length) :
    (subDigitLists xs ys borrow).1.length = xs.length := by
  induction xs generalizing ys borrow with
  | nil =>
      cases ys <;> simp_all [subDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          simp only [subDigitLists, List.length_cons]
          rw [ih hlength']

/-! ## The procedure -/

/-- The final carry out of the fixed-width addition pass. -/
def addModCarry (xs ys : List Nat) : Nat := (addDigitLists xs ys 0).2

/-- The wrapped sum limbs and final borrow of the conditional-subtraction
pass. -/
def addModCandidate (xs ys ms : List Nat) : List Nat × Nat :=
  subDigitLists (addDigitLists xs ys 0).1 ms 0

/-- The final borrow out of the conditional-subtraction pass. -/
def addModBorrow (xs ys ms : List Nat) : Nat := (addModCandidate xs ys ms).2

/-- The selected result limbs: the subtraction candidate when the addition
carried or the subtraction did not borrow, else the wrapped sum limbs. -/
def addModResult (xs ys ms : List Nat) : List Nat :=
  if addModCarry xs ys = 1 ∨ addModBorrow xs ys ms = 0 then
    (addModCandidate xs ys ms).1
  else (addDigitLists xs ys 0).1

/-! ## Carry and borrow side conditions -/

theorem addModCarry_le_one {xs ys : List Nat}
    (hlength : xs.length = ys.length)
    (hxs : ∀ d ∈ xs, d < radix) (hys : ∀ d ∈ ys, d < radix) :
    addModCarry xs ys ≤ 1 :=
  addDigitLists_carry_le_one hlength hxs hys (by omega)

theorem addModBorrow_le_one {xs ys ms : List Nat}
    (hlength : xs.length = ys.length) (hmslen : ys.length = ms.length) :
    addModBorrow xs ys ms ≤ 1 := by
  have hsumlen : (addDigitLists xs ys 0).1.length = ms.length := by
    rw [length_addDigitLists_left hlength, hlength, hmslen]
  exact subDigitLists_borrow_le_one hsumlen (by omega)

/-! ## Correctness -/

/-- Value-level core of `addMod`, stated over the four pieces the procedure
computes, so that callers can supply whatever syntactic form they have. -/
theorem addMod_value_core {xs ys ms sum cand : List Nat} {carry borrow : Nat}
    (hlen : xs.length = ys.length) (hmslen : ys.length = ms.length)
    (hxs : ∀ d ∈ xs, d < radix) (hys : ∀ d ∈ ys, d < radix)
    (hms : ∀ d ∈ ms, d < radix)
    (hsumdef : addDigitLists xs ys 0 = (sum, carry))
    (hcanddef : subDigitLists sum ms 0 = (cand, borrow))
    (hx : Nat.ofDigits radix xs < Nat.ofDigits radix ms)
    (hy : Nat.ofDigits radix ys < Nat.ofDigits radix ms) :
    Nat.ofDigits radix (if carry = 1 ∨ borrow = 0 then cand else sum) =
      (Nat.ofDigits radix xs + Nat.ofDigits radix ys) % Nat.ofDigits radix ms := by
  have hv1 := addDigitLists_value (carry := 0) hlen
  rw [hsumdef] at hv1
  dsimp only at hv1
  rw [hlen.trans hmslen, Nat.add_zero] at hv1
  have hv2 : carry ≤ 1 := by
    have h := addDigitLists_carry_le_one (carry := 0) hlen hxs hys
      (by omega)
    rw [hsumdef] at h
    exact h
  have hv3 : ∀ d ∈ sum, d < radix := fun d hd =>
    addDigitLists_digits_lt (carry := 0) (digit := d) (by rw [hsumdef]; exact hd)
  have hv4 : sum.length = ms.length := by
    have h := length_addDigitLists_left (carry := 0) hlen
    rw [hsumdef] at h
    exact h.trans (hlen.trans hmslen)
  have hv5 := subDigitLists_value (xs := sum) (ys := ms) (borrow := 0) hv4 hv3
    hms (by omega)
  rw [hcanddef] at hv5
  dsimp only at hv5
  rw [Nat.add_zero, hv4] at hv5
  have hv6 : borrow ≤ 1 := by
    have h := subDigitLists_borrow_le_one (xs := sum) (ys := ms) (borrow := 0) hv4
      (by omega)
    rw [hcanddef] at h
    exact h
  have hv7 : ∀ d ∈ cand, d < radix := fun d hd =>
    subDigitLists_digits_lt (xs := sum) (ys := ms) (borrow := 0) hv4 hv3 hms
      (by omega) (by rw [hcanddef]; exact hd)
  have hR : Nat.ofDigits radix ms < radix ^ ms.length :=
    Nat.ofDigits_lt_base_pow_length radix_gt_one hms
  have hcandlen : cand.length = ms.length := by
    have h := length_subDigitLists_left (xs := sum) (ys := ms) (borrow := 0) hv4
    rw [hcanddef] at h
    dsimp only at h
    exact h.trans hv4
  have hC : Nat.ofDigits radix cand < radix ^ ms.length := by
    have h := Nat.ofDigits_lt_base_pow_length radix_gt_one hv7
    rw [hcandlen] at h
    exact h
  have hS : Nat.ofDigits radix sum < radix ^ ms.length := by
    have h := Nat.ofDigits_lt_base_pow_length radix_gt_one hv3
    rw [hv4] at h
    exact h
  have hslt : Nat.ofDigits radix xs + Nat.ofDigits radix ys <
      2 * Nat.ofDigits radix ms := by
    have h := masked_sum_lt_twice (take := 1) hx hy (by norm_num)
    simpa using h
  rw [mod_eq_cond_sub hslt]
  rcases (show carry = 0 ∨ carry = 1 by omega) with hc | hc
  · subst hc
    rcases (show borrow = 0 ∨ borrow = 1 by omega) with hb | hb
    · subst hb
      rw [if_pos (Or.inr rfl)]
      by_cases hltm : Nat.ofDigits radix xs + Nat.ofDigits radix ys <
          Nat.ofDigits radix ms
      · rw [if_pos hltm]; omega
      · rw [if_neg hltm]; omega
    · subst hb
      rw [if_neg (by omega)]
      by_cases hltm : Nat.ofDigits radix xs + Nat.ofDigits radix ys <
          Nat.ofDigits radix ms
      · rw [if_pos hltm]; omega
      · rw [if_neg hltm]; omega
  · subst hc
    rcases (show borrow = 0 ∨ borrow = 1 by omega) with hb | hb
    · subst hb
      rw [if_pos (Or.inl rfl)]
      by_cases hltm : Nat.ofDigits radix xs + Nat.ofDigits radix ys <
          Nat.ofDigits radix ms
      · rw [if_pos hltm]; omega
      · rw [if_neg hltm]; omega
    · subst hb
      rw [if_pos (Or.inl rfl)]
      by_cases hltm : Nat.ofDigits radix xs + Nat.ofDigits radix ys <
          Nat.ofDigits radix ms
      · rw [if_pos hltm]; omega
      · rw [if_neg hltm]; omega

/-- The `addMod` procedure's result list represents the modular sum. -/
theorem addModResult_value {xs ys ms : List Nat}
    (h1 : xs.length = ms.length) (h2 : ys.length = ms.length)
    (hxs : ∀ d ∈ xs, d < radix) (hys : ∀ d ∈ ys, d < radix)
    (hms : ∀ d ∈ ms, d < radix)
    (hx : Nat.ofDigits radix xs < Nat.ofDigits radix ms)
    (hy : Nat.ofDigits radix ys < Nat.ofDigits radix ms) :
    Nat.ofDigits radix (addModResult xs ys ms) =
      (Nat.ofDigits radix xs + Nat.ofDigits radix ys) % Nat.ofDigits radix ms := by
  simp only [addModResult, addModCarry, addModBorrow, addModCandidate]
  exact addMod_value_core (h1.trans h2.symm) h2 hxs hys hms rfl rfl hx hy

/-- The `≤`-relaxed core: the second operand may equal the modulus (the ONE
region's `1` against `m = 1`).  The strict bound is only used to keep the
pre-reduction sum below twice the modulus, which `≤` still guarantees. -/
theorem addMod_value_core_le {xs ys ms sum cand : List Nat} {carry borrow : Nat}
    (hlen : xs.length = ys.length) (hmslen : ys.length = ms.length)
    (hxs : ∀ d ∈ xs, d < radix) (hys : ∀ d ∈ ys, d < radix)
    (hms : ∀ d ∈ ms, d < radix)
    (hsumdef : addDigitLists xs ys 0 = (sum, carry))
    (hcanddef : subDigitLists sum ms 0 = (cand, borrow))
    (hx : Nat.ofDigits radix xs < Nat.ofDigits radix ms)
    (hy : Nat.ofDigits radix ys ≤ Nat.ofDigits radix ms) :
    Nat.ofDigits radix (if carry = 1 ∨ borrow = 0 then cand else sum) =
      (Nat.ofDigits radix xs + Nat.ofDigits radix ys) % Nat.ofDigits radix ms := by
  have hv1 := addDigitLists_value (carry := 0) hlen
  rw [hsumdef] at hv1
  dsimp only at hv1
  rw [hlen.trans hmslen, Nat.add_zero] at hv1
  have hv2 : carry ≤ 1 := by
    have h := addDigitLists_carry_le_one (carry := 0) hlen hxs hys
      (by omega)
    rw [hsumdef] at h
    exact h
  have hv3 : ∀ d ∈ sum, d < radix := fun d hd =>
    addDigitLists_digits_lt (carry := 0) (digit := d) (by rw [hsumdef]; exact hd)
  have hv4 : sum.length = ms.length := by
    have h := length_addDigitLists_left (carry := 0) hlen
    rw [hsumdef] at h
    exact h.trans (hlen.trans hmslen)
  have hv5 := subDigitLists_value (xs := sum) (ys := ms) (borrow := 0) hv4 hv3
    hms (by omega)
  rw [hcanddef] at hv5
  dsimp only at hv5
  rw [Nat.add_zero, hv4] at hv5
  have hv6 : borrow ≤ 1 := by
    have h := subDigitLists_borrow_le_one (xs := sum) (ys := ms) (borrow := 0) hv4
      (by omega)
    rw [hcanddef] at h
    exact h
  have hv7 : ∀ d ∈ cand, d < radix := fun d hd =>
    subDigitLists_digits_lt (xs := sum) (ys := ms) (borrow := 0) hv4 hv3 hms
      (by omega) (by rw [hcanddef]; exact hd)
  have hR : Nat.ofDigits radix ms < radix ^ ms.length :=
    Nat.ofDigits_lt_base_pow_length radix_gt_one hms
  have hcandlen : cand.length = ms.length := by
    have h := length_subDigitLists_left (xs := sum) (ys := ms) (borrow := 0) hv4
    rw [hcanddef] at h
    dsimp only at h
    exact h.trans hv4
  have hC : Nat.ofDigits radix cand < radix ^ ms.length := by
    have h := Nat.ofDigits_lt_base_pow_length radix_gt_one hv7
    rw [hcandlen] at h
    exact h
  have hS : Nat.ofDigits radix sum < radix ^ ms.length := by
    have h := Nat.ofDigits_lt_base_pow_length radix_gt_one hv3
    rw [hv4] at h
    exact h
  have hslt : Nat.ofDigits radix xs + Nat.ofDigits radix ys <
      2 * Nat.ofDigits radix ms := by omega
  rw [mod_eq_cond_sub hslt]
  rcases (show carry = 0 ∨ carry = 1 by omega) with hc | hc
  · subst hc
    rcases (show borrow = 0 ∨ borrow = 1 by omega) with hb | hb
    · subst hb
      rw [if_pos (Or.inr rfl)]
      by_cases hltm : Nat.ofDigits radix xs + Nat.ofDigits radix ys <
          Nat.ofDigits radix ms
      · rw [if_pos hltm]; omega
      · rw [if_neg hltm]; omega
    · subst hb
      rw [if_neg (by omega)]
      by_cases hltm : Nat.ofDigits radix xs + Nat.ofDigits radix ys <
          Nat.ofDigits radix ms
      · rw [if_pos hltm]; omega
      · rw [if_neg hltm]; omega
  · subst hc
    rcases (show borrow = 0 ∨ borrow = 1 by omega) with hb | hb
    · subst hb
      rw [if_pos (Or.inl rfl)]
      by_cases hltm : Nat.ofDigits radix xs + Nat.ofDigits radix ys <
          Nat.ofDigits radix ms
      · rw [if_pos hltm]; omega
      · rw [if_neg hltm]; omega
    · subst hb
      rw [if_pos (Or.inl rfl)]
      by_cases hltm : Nat.ofDigits radix xs + Nat.ofDigits radix ys <
          Nat.ofDigits radix ms
      · rw [if_pos hltm]; omega
      · rw [if_neg hltm]; omega

/-- The `≤`-relaxed modular-sum value: the second operand may equal the
modulus. -/
theorem addModResult_value_le {xs ys ms : List Nat}
    (h1 : xs.length = ms.length) (h2 : ys.length = ms.length)
    (hxs : ∀ d ∈ xs, d < radix) (hys : ∀ d ∈ ys, d < radix)
    (hms : ∀ d ∈ ms, d < radix)
    (hx : Nat.ofDigits radix xs < Nat.ofDigits radix ms)
    (hy : Nat.ofDigits radix ys ≤ Nat.ofDigits radix ms) :
    Nat.ofDigits radix (addModResult xs ys ms) =
      (Nat.ofDigits radix xs + Nat.ofDigits radix ys) % Nat.ofDigits radix ms := by
  simp only [addModResult, addModCarry, addModBorrow, addModCandidate]
  exact addMod_value_core_le (h1.trans h2.symm) h2 hxs hys hms rfl rfl hx hy

/-- The result list has the common limb width. -/
theorem addModResult_length {xs ys ms : List Nat}
    (h1 : xs.length = ms.length) (h2 : ys.length = ms.length) :
    (addModResult xs ys ms).length = ms.length := by
  simp only [addModResult, addModCarry, addModBorrow, addModCandidate]
  split_ifs
  · rw [length_subDigitLists_left
      (by rw [length_addDigitLists_left (h1.trans h2.symm), h1]),
      length_addDigitLists_left (h1.trans h2.symm), h1]
  · rw [length_addDigitLists_left (h1.trans h2.symm), h1]

/-- Every limb of the result is below the radix. -/
theorem addModResult_digits_lt {xs ys ms : List Nat}
    (h1 : xs.length = ms.length) (h2 : ys.length = ms.length)
    (hms : ∀ d ∈ ms, d < radix) {d : Nat}
    (hd : d ∈ addModResult xs ys ms) :
    d < radix := by
  simp only [addModResult, addModCarry, addModBorrow, addModCandidate] at hd
  split_ifs at hd
  · exact subDigitLists_digits_lt
      (by rw [length_addDigitLists_left (h1.trans h2.symm), h1])
      (fun d' hd' =>
        addDigitLists_digits_lt (carry := 0) (digit := d') hd')
      hms (by omega) hd
  · exact addDigitLists_digits_lt (carry := 0) hd

/-- The selection condition of the procedure is exactly the mathematical
"the sum reached the modulus" test (cf. `Limbs.useSub_iff`). -/
theorem addMod_useSub_iff {xs ys ms : List Nat}
    (h1 : xs.length = ms.length) (h2 : ys.length = ms.length)
    (hxs : ∀ d ∈ xs, d < radix) (hys : ∀ d ∈ ys, d < radix)
    (hms : ∀ d ∈ ms, d < radix)
    (hx : Nat.ofDigits radix xs < Nat.ofDigits radix ms)
    (hy : Nat.ofDigits radix ys < Nat.ofDigits radix ms) :
    (addModCarry xs ys = 1 ∨ addModBorrow xs ys ms = 0) ↔
      Nat.ofDigits radix ms ≤ Nat.ofDigits radix xs + Nat.ofDigits radix ys := by
  have hlen : xs.length = ys.length := h1.trans h2.symm
  rcases hsum : addDigitLists xs ys 0 with ⟨sum, carry⟩
  rcases hcand : subDigitLists sum ms 0 with ⟨cand, borrow⟩
  have hv1 := addDigitLists_value (carry := 0) hlen
  rw [hsum] at hv1
  dsimp only at hv1
  rw [hlen.trans h2, Nat.add_zero] at hv1
  have hv2 : carry ≤ 1 := by
    have h := addDigitLists_carry_le_one (carry := 0) hlen hxs hys (by omega)
    rw [hsum] at h
    exact h
  have hv3 : ∀ d ∈ sum, d < radix := fun d hd =>
    addDigitLists_digits_lt (carry := 0) (digit := d) (by rw [hsum]; exact hd)
  have hv4 : sum.length = ms.length := by
    have h := length_addDigitLists_left (carry := 0) hlen
    rw [hsum] at h
    exact h.trans (hlen.trans h2)
  have hv5 := subDigitLists_value (xs := sum) (ys := ms) (borrow := 0) hv4 hv3
    hms (by omega)
  rw [hcand] at hv5
  dsimp only at hv5
  rw [Nat.add_zero, hv4] at hv5
  have hv6 : borrow ≤ 1 := by
    have h := subDigitLists_borrow_le_one (xs := sum) (ys := ms) (borrow := 0)
      hv4 (by omega)
    rw [hcand] at h
    exact h
  have hR : Nat.ofDigits radix ms < radix ^ ms.length :=
    Nat.ofDigits_lt_base_pow_length radix_gt_one hms
  have hC : Nat.ofDigits radix cand < radix ^ ms.length := by
    have hcandlen : cand.length = ms.length := by
      have h := length_subDigitLists_left (xs := sum) (ys := ms) (borrow := 0)
        hv4
      rw [hcand] at h
      dsimp only at h
      exact h.trans hv4
    have h := Nat.ofDigits_lt_base_pow_length radix_gt_one
      (fun d hd =>
        subDigitLists_digits_lt (xs := sum) (ys := ms) (borrow := 0) hv4 hv3
          hms (by omega) (by rw [hcand]; exact hd))
    rw [hcandlen] at h
    exact h
  simp only [addModCarry, addModBorrow, addModCandidate, hsum]
  rw [hcand]
  rcases (show carry = 0 ∨ carry = 1 by omega) with hc | hc
  · subst hc
    rcases (show borrow = 0 ∨ borrow = 1 by omega) with hb | hb <;> subst hb <;>
      omega
  · subst hc
    rcases (show borrow = 0 ∨ borrow = 1 by omega) with hb | hb <;> subst hb <;>
      omega

/-- The doubling special case (`src = dst`). -/
theorem doubleMod_value {xs ms : List Nat}
    (hlen : xs.length = ms.length)
    (hxs : ∀ d ∈ xs, d < radix) (hms : ∀ d ∈ ms, d < radix)
    (hx : Nat.ofDigits radix xs < Nat.ofDigits radix ms) :
    Nat.ofDigits radix (addModResult xs xs ms) =
      (2 * Nat.ofDigits radix xs) % Nat.ofDigits radix ms := by
  rw [addModResult_value hlen hlen hxs hxs hms hx hx]
  have h : Nat.ofDigits radix xs + Nat.ofDigits radix xs = 2 * Nat.ofDigits radix xs :=
    by ring
  rw [h]

end Challenge.Modexp.Submission.Proof.AddModMath
