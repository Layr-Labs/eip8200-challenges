/-!
# Montgomery CIOS arithmetic draft (EVM-free, core-Lean only)

Private draft for the EIP-8200 MODEXP Montgomery optimization. It models the
inner word-product loop of
`benchmark-results/modexp/montgomery/montgomery_proto.py` over radix `2^256`
limbs and proves the load-bearing limb facts that the Yul program needs:

* `fullMul_value` / `fullHi_lt`: the `MUL`/`MULMOD`-based full multiply
  (`fullMulHi` in `montgomery.yul`) is an exact 512-bit product;
* `three_term_carry`: the two EVM `LT` overflow tests compute exactly the
  carry quotient of the three-term sum for *any* incoming carry `c < B`
  (generalizes `Limbs.addCarryBits`, which assumes `carry ≤ 1`);
* `step_carry_le`: the running carry stays `≤ word` (hence `< B`, so the
  Yul `carry := add(hi, c)` never wraps);
* `addWordInner_value` + `length_addWordInner`: the inner loop stores
  exactly `old + word * X + carry_in` across the consumed prefix.

Deliberately self-contained (no imports): it typechecks with the bare pinned
toolchain via `lean <this file>` from a worktree root, with no Lake
dependencies. Bridges to the submission library are stated at the bottom as
comments; the outer CIOS invariant (`T < 2m`, quotient selection, final
subtraction, Newton inversion, `R^2` doubling) is specified with exact
induction plans in `muse-proof.md` and needs Mathlib tactics
(`nlinarith`, `interval_cases`) plus the Lake environment, so it is
intentionally *not* claimed here. No unfinished proof placeholders,
project-defined axioms, `native_decide`, or `unsafe` appear in this file.
-/

namespace Challenge.Modexp.Submission.Proofs.Montgomery.WordArithmetic

def montRadix : Nat := 2 ^ 256

def fullLo (x y : Nat) : Nat := (x * y) % montRadix

def fullHi (x y : Nat) : Nat := (x * y) / montRadix

def limbVal : List Nat → Nat
  | [] => 0
  | d :: ds => d + montRadix * limbVal ds

def addWordInner : List Nat → List Nat → Nat → Nat → List Nat × Nat
  | [], _, _, carry => ([], carry)
  | _ :: _, [], _, carry => ([], carry)
  | xj :: xs, t0 :: ts, word, carry =>
    ((t0 + fullLo xj word + carry) % montRadix
      :: (addWordInner xs ts word
        (fullHi xj word + (t0 + fullLo xj word + carry) / montRadix)).1,
      (addWordInner xs ts word
        (fullHi xj word + (t0 + fullLo xj word + carry) / montRadix)).2)

theorem length_addWordInner (xs ts : List Nat) (word carry : Nat)
    (hlength : xs.length = ts.length) :
    (addWordInner xs ts word carry).1.length = xs.length := by
  induction xs generalizing ts carry with
  | nil =>
    cases ts with
    | nil => simp [addWordInner]
    | cons t0 ts => simp at hlength
  | cons xj xs ih =>
    cases ts with
    | nil => simp at hlength
    | cons t0 ts =>
      have hlength' : xs.length = ts.length := by simpa using hlength
      simp [addWordInner, ih _ _ hlength']

theorem radix_pos : 0 < montRadix := by unfold montRadix; decide

theorem fullMul_value (x y : Nat) :
    fullLo x y + montRadix * fullHi x y = x * y := by
  unfold fullLo fullHi
  exact Nat.mod_add_div _ _

theorem three_term_carry (x y c : Nat)
    (hx : x < montRadix) (hy : y < montRadix) (hc : c < montRadix) :
    ((x + y) % montRadix + c) % montRadix = (x + y + c) % montRadix ∧
    (if (x + y) % montRadix < x then 1 else 0) +
      (if ((x + y) % montRadix + c) % montRadix < (x + y) % montRadix
        then 1 else 0)
      = (x + y + c) / montRadix := by
  have hB := radix_pos
  have hsB : (x + y) % montRadix < montRadix := Nat.mod_lt _ hB
  have hadd_mod :
      ((x + y) % montRadix + c) % montRadix = (x + y + c) % montRadix := by
    have h := Nat.add_mod (x + y) c montRadix
    rw [Nat.mod_eq_of_lt hc] at h
    exact h.symm
  have hq : (x + y + c) / montRadix
      = (x + y) / montRadix + ((x + y) % montRadix + c) / montRadix := by
    have hdecomp : x + y + c
        = ((x + y) % montRadix + c) + montRadix * ((x + y) / montRadix) := by
      have h := Nat.mod_add_div (x + y) montRadix
      omega
    rw [hdecomp, Nat.add_mul_div_left _ _ hB]
    omega
  have hc1 : (if (x + y) % montRadix < x then 1 else 0)
      = (x + y) / montRadix := by
    by_cases h1 : x + y < montRadix
    · rw [Nat.mod_eq_of_lt h1, if_neg (by omega), Nat.div_eq_of_lt h1]
    · have h1le : montRadix ≤ x + y := by omega
      have hpos1 : x + y - montRadix < x := by omega
      have e1 : (x + y) % montRadix = x + y - montRadix := by
        rw [Nat.mod_eq_sub_mod h1le, Nat.mod_eq_of_lt (by omega)]
      rw [e1, if_pos hpos1]
      exact (Nat.div_eq_of_lt_le (by omega : 1 * montRadix ≤ x + y)
        (by omega : x + y < (1 + 1) * montRadix)).symm
  have hc2 : (if ((x + y) % montRadix + c) % montRadix < (x + y) % montRadix
        then 1 else 0)
      = ((x + y) % montRadix + c) / montRadix := by
    by_cases h2 : (x + y) % montRadix + c < montRadix
    · rw [Nat.mod_eq_of_lt h2, if_neg (by omega), Nat.div_eq_of_lt h2]
    · have h2le : montRadix ≤ (x + y) % montRadix + c := by omega
      have hpos2 : (x + y) % montRadix + c - montRadix < (x + y) % montRadix := by omega
      have e2 : ((x + y) % montRadix + c) % montRadix
          = (x + y) % montRadix + c - montRadix := by
        rw [Nat.mod_eq_sub_mod h2le, Nat.mod_eq_of_lt (by omega)]
      rw [e2, if_pos hpos2]
      exact (Nat.div_eq_of_lt_le
        (by omega : 1 * montRadix ≤ (x + y) % montRadix + c)
        (by omega : (x + y) % montRadix + c < (1 + 1) * montRadix)).symm
  exact ⟨hadd_mod, by rw [hq, ← hc1, ← hc2]⟩

theorem step_carry_le (x t0 word carry : Nat)
    (hx : x < montRadix) (ht : t0 < montRadix) (hw : word < montRadix)
    (hc : carry ≤ word) :
    fullHi x word + (t0 + fullLo x word + carry) / montRadix ≤ word := by
  have hB := radix_pos
  have _hcB : carry < montRadix := Nat.lt_of_le_of_lt hc hw
  have hfull := fullMul_value x word
  have hsucc : x + 1 ≤ montRadix := by omega
  have hmul : (x + 1) * word ≤ montRadix * word :=
    Nat.mul_le_mul hsucc (Nat.le_refl word)
  have hexpand : (x + 1) * word = x * word + word := by
    rw [Nat.add_mul, Nat.one_mul]
  have hdecomp : x * word + t0 + carry
      = montRadix * (fullHi x word + (t0 + fullLo x word + carry) / montRadix)
        + (t0 + fullLo x word + carry) % montRadix := by
    have e1 : x * word = fullLo x word + montRadix * fullHi x word :=
      hfull.symm
    have e2 : t0 + fullLo x word + carry
        = (t0 + fullLo x word + carry) % montRadix
          + montRadix * ((t0 + fullLo x word + carry) / montRadix) :=
      (Nat.mod_add_div _ _).symm
    rw [e1, Nat.mul_add]
    omega
  have hbound : x * word + t0 + carry
      ≤ montRadix * word + (montRadix - 1) := by
    omega
  have hstep : montRadix * (fullHi x word + (t0 + fullLo x word + carry) / montRadix)
      ≤ montRadix * word + (montRadix - 1) := by
    omega
  have hexpand2 : montRadix * (word + 1) = montRadix * word + montRadix := by
    rw [Nat.mul_add, Nat.mul_one]
  have hlt : montRadix * (fullHi x word + (t0 + fullLo x word + carry) / montRadix)
      < montRadix * (word + 1) := by
    omega
  have hfin : fullHi x word + (t0 + fullLo x word + carry) / montRadix
      < word + 1 :=
    Nat.lt_of_mul_lt_mul_left hlt
  omega

theorem addWordInner_value (xs ts : List Nat) (word carry : Nat)
    (hlength : xs.length = ts.length)
    (hxs : ∀ d ∈ xs, d < montRadix)
    (hts : ∀ d ∈ ts, d < montRadix)
    (hw : word < montRadix)
    (hc : carry ≤ word) :
    limbVal (addWordInner xs ts word carry).1
      + montRadix ^ xs.length * (addWordInner xs ts word carry).2
      = limbVal xs * word + limbVal ts + carry := by
  induction xs generalizing ts carry with
  | nil =>
    cases ts with
    | nil => simp [addWordInner, limbVal]
    | cons t0 ts => simp at hlength
  | cons xj xs ih =>
    cases ts with
    | nil => simp at hlength
    | cons t0 ts =>
      have hlength' : xs.length = ts.length := by simpa using hlength
      have hxj : xj < montRadix := hxs xj (by simp)
      have ht0 : t0 < montRadix := hts t0 (by simp)
      have hcarry' : fullHi xj word + (t0 + fullLo xj word + carry) / montRadix
          ≤ word :=
        step_carry_le xj t0 word carry hxj ht0 hw hc
      have hnext := ih ts
        (fullHi xj word + (t0 + fullLo xj word + carry) / montRadix) hlength'
        (fun d hd => hxs d (by simp [hd]))
        (fun d hd => hts d (by simp [hd])) hcarry'
      have hfull := fullMul_value xj word
      have hdiv := Nat.mod_add_div (t0 + fullLo xj word + carry) montRadix
      have hscaled := congrArg (fun v => montRadix * v) hnext
      simp only [Nat.mul_add] at hscaled
      simp only [addWordInner, limbVal, List.length_cons,
        Nat.add_mul, Nat.mul_assoc] at hscaled ⊢
      rw [Nat.pow_add_one, Nat.mul_comm (montRadix ^ xs.length) montRadix,
        Nat.mul_assoc montRadix (montRadix ^ xs.length)]
      omega

/-
Bridge notes for integration under the Lake environment (not checked here):

* `montRadix = Challenge.Modexp.Submission.Proofs.Limbs.radix` by `rfl`
  (both are `2 ^ 256`).
* `limbVal ds = Nat.ofDigits montRadix ds` by induction on `ds`
  (same recursion as `Nat.ofDigits`).
* `addWordInner` is the inner `j`-loop of `_add_word_product` in
  `montgomery_proto.py` restricted to the consumed prefix; the top two-limb
  fold and the outer CIOS induction (`T < 2 * m`, Lemma INV in
  `muse-proof.md`) are the next layer and need Mathlib tactics, so they live
  in the proof draft, not in this machine-checked core.
-/

end Challenge.Modexp.Submission.Proofs.Montgomery.WordArithmetic
