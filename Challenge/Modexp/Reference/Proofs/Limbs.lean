import Challenge.Modexp.Reference.Proofs.Algorithm
import Challenge.EvmProof.Bytes
import Mathlib.Data.Nat.Digits.Lemmas
set_option warningAsError true
/-!
# Little-endian 256-bit limbs

The general MODEXP path stores an arbitrary-precision integer as consecutive
EVM words, least-significant word first.  This module gives that memory layout
a small mathematical interface.  It deliberately does not mention the
reference control flow, so all helper and loop certificates can share it.
-/

namespace Challenge.Modexp.Reference.Proofs.Limbs

open EvmSemantics

/-- Radix of one EVM word. -/
def radix : Nat := 2 ^ 256

/-- Number of 256-bit limbs required for a byte width. -/
def limbCount (width : Nat) : Nat := (width + 31) / 32

/-- The fixed-width little-endian radix expansion of `value`. -/
def limbDigits (count value : Nat) : List Nat :=
  Nat.digitsAppend radix count value

/-- Consecutive little-endian EVM words read from memory. -/
def memoryLimbs (memory : ByteArray) (ptr count : Nat) : List Nat :=
  (List.range count).map fun i =>
    (MachineState.readWord memory (ptr + 32 * i)).toNat

/-- `memory[ptr .. ptr + 32*count]` is the fixed-width limb encoding of
`value`.  The explicit range premise rules out truncating high limbs. -/
def Represents (memory : ByteArray) (ptr count value : Nat) : Prop :=
  value < radix ^ count ∧ memoryLimbs memory ptr count = limbDigits count value

theorem radix_eq : radix = 256 ^ 32 := by
  simp [radix]

theorem radix_gt_one : 1 < radix := by
  norm_num [radix]

theorem radix_pos : 0 < radix := by
  exact Nat.zero_lt_of_lt radix_gt_one

theorem limbCount_le_32 (width : Nat) (hwidth : width ≤ 1024) :
    limbCount width ≤ 32 := by
  unfold limbCount
  omega

theorem width_le_limbs (width : Nat) : width ≤ 32 * limbCount width := by
  unfold limbCount
  omega

theorem limbCount_pos {width : Nat} (hwidth : 0 < width) :
    0 < limbCount width := by
  unfold limbCount
  omega

theorem pow_radix (count : Nat) :
    radix ^ count = 256 ^ (32 * count) := by
  rw [radix_eq, ← Nat.pow_mul]

theorem byteValue_fits_limbs (input : ByteArray) (offset width : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded input offset width <
      radix ^ limbCount width := by
  have hbytes := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
    input offset width
  have hwidth := width_le_limbs width
  have hpow : 256 ^ width ≤ 256 ^ (32 * limbCount width) := by
    exact Nat.pow_le_pow_right (by omega) hwidth
  rw [pow_radix]
  exact hbytes.trans_le hpow

@[simp] theorem length_limbDigits {count value : Nat}
    (hvalue : value < radix ^ count) :
    (limbDigits count value).length = count := by
  exact Nat.length_digitsAppend radix_gt_one count hvalue

theorem limbDigits_lt {count value digit : Nat}
    (hdigit : digit ∈ limbDigits count value) : digit < radix := by
  exact Nat.lt_of_mem_digitsAppend radix_gt_one count digit hdigit

theorem value_limbDigits (count value : Nat) :
    Nat.ofDigits radix (limbDigits count value) = value := by
  rw [limbDigits, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
    Nat.ofDigits_digits]

theorem memoryLimb_lt (memory : ByteArray) (ptr count : Nat)
    {digit : Nat} (hdigit : digit ∈ memoryLimbs memory ptr count) :
    digit < radix := by
  simp only [memoryLimbs, List.mem_map] at hdigit
  rcases hdigit with ⟨i, _, rfl⟩
  exact (MachineState.readWord memory (ptr + 32 * i)).val.isLt

@[simp] theorem length_memoryLimbs (memory : ByteArray) (ptr count : Nat) :
    (memoryLimbs memory ptr count).length = count := by
  simp [memoryLimbs]

theorem value_of_represents {memory : ByteArray} {ptr count value : Nat}
    (hrep : Represents memory ptr count value) :
    Nat.ofDigits radix (memoryLimbs memory ptr count) = value := by
  rw [hrep.2, value_limbDigits]

theorem represents_value_unique {memory : ByteArray} {ptr count a b : Nat}
    (ha : Represents memory ptr count a) (hb : Represents memory ptr count b) :
    a = b := by
  rw [← value_of_represents ha, ← value_of_represents hb]

theorem represents_iff_value {memory : ByteArray} {ptr count value : Nat}
    (hvalue : value < radix ^ count) :
    Represents memory ptr count value ↔
      Nat.ofDigits radix (memoryLimbs memory ptr count) = value := by
  constructor
  · exact value_of_represents
  · intro heq
    refine ⟨hvalue, ?_⟩
    apply Nat.ofDigits_inj_of_len_eq radix_gt_one
    · rw [length_memoryLimbs, length_limbDigits hvalue]
    · exact fun digit hdigit => memoryLimb_lt _ _ _ hdigit
    · exact fun digit hdigit => limbDigits_lt hdigit
    · rw [heq, value_limbDigits]

/-! ## Arithmetic used by `addMaskedMod`

The bytecode adds either zero or one residue and then performs one conditional
subtraction.  These lemmas isolate the mathematical reason one subtraction is
enough from the word-by-word carry and borrow implementation proved below the
bytecode layer.
-/

theorem masked_sum_lt_twice {x y take modulus : Nat}
    (hx : x < modulus) (hy : y < modulus) (htake : take ≤ 1) :
    x + take * y < 2 * modulus := by
  interval_cases take <;> simp_all <;> omega

theorem mod_eq_cond_sub {total modulus : Nat}
    (htotal : total < 2 * modulus) :
    total % modulus = if total < modulus then total else total - modulus := by
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem masked_sum_mod_eq_cond_sub {x y take modulus : Nat}
    (hx : x < modulus) (hy : y < modulus) (htake : take ≤ 1) :
    (x + take * y) % modulus =
      if x + take * y < modulus then x + take * y
      else x + take * y - modulus := by
  exact mod_eq_cond_sub (masked_sum_lt_twice hx hy htake)

/-- The bytecode selects its subtraction candidate exactly when the
mathematical sum is at least the modulus.  The first disjunct is the final
carry out of the fixed-width addition; the second is a borrow-free comparison
of the wrapped sum with the modulus. -/
theorem useSub_iff {total modulus bound : Nat} (hmodulus : modulus < bound) :
    (bound ≤ total ∨ modulus ≤ total % bound) ↔ modulus ≤ total := by
  constructor
  · rintro (hcarry | hwrapped)
    · exact hmodulus.le.trans hcarry
    · exact hwrapped.trans (Nat.mod_le total bound)
  · intro htotal
    by_cases hcarry : bound ≤ total
    · exact Or.inl hcarry
    · right
      rwa [Nat.mod_eq_of_lt (Nat.lt_of_not_ge hcarry)]

/-! ## Canonical carry recurrence -/

/-- Add two equally-sized little-endian limb lists, returning the result limbs
and the carry beyond their common width. -/
def addDigitLists : List Nat → List Nat → Nat → List Nat × Nat
  | [], [], carry => ([], carry)
  | x :: xs, y :: ys, carry =>
      let total := x + y + carry
      let next := addDigitLists xs ys (total / radix)
      (total % radix :: next.1, next.2)
  | _, _, carry => ([], carry)

theorem length_addDigitLists_left {xs ys : List Nat} {carry : Nat}
    (hlength : xs.length = ys.length) :
    (addDigitLists xs ys carry).1.length = xs.length := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          simp [addDigitLists, ih hlength']

theorem addDigitLists_value {xs ys : List Nat} {carry : Nat}
    (hlength : xs.length = ys.length) :
    Nat.ofDigits radix (addDigitLists xs ys carry).1 +
        radix ^ xs.length * (addDigitLists xs ys carry).2 =
      Nat.ofDigits radix xs + Nat.ofDigits radix ys + carry := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          let total := x + y + carry
          let next := addDigitLists xs ys (total / radix)
          have hnext := ih (carry := total / radix) hlength'
          have hdivide := Nat.mod_add_div total radix
          simp only [addDigitLists, Nat.ofDigits_cons,
            List.length_cons, pow_succ]
          simp only [total] at hnext hdivide
          nlinarith

theorem addDigitLists_digits_lt {xs ys : List Nat} {carry digit : Nat}
    (hdigit : digit ∈ (addDigitLists xs ys carry).1) : digit < radix := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all [addDigitLists]
      | cons y ys =>
          simp only [addDigitLists, List.mem_cons] at hdigit
          rcases hdigit with rfl | hdigit
          · exact Nat.mod_lt _ radix_pos
          · exact ih hdigit

theorem addDigitLists_carry_le_one {xs ys : List Nat} {carry : Nat}
    (hlength : xs.length = ys.length)
    (hxs : ∀ digit ∈ xs, digit < radix)
    (hys : ∀ digit ∈ ys, digit < radix) (hcarry : carry ≤ 1) :
    (addDigitLists xs ys carry).2 ≤ 1 := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          have hx : x < radix := hxs x (by simp)
          have hy : y < radix := hys y (by simp)
          have hquotient : (x + y + carry) / radix ≤ 1 := by
            rw [Nat.div_le_iff_le_mul radix_pos]
            omega
          simp only [addDigitLists]
          exact ih hlength' (fun digit hdigit => hxs digit (by simp [hdigit]))
            (fun digit hdigit => hys digit (by simp [hdigit])) hquotient

theorem ofDigits_map_mul (digits : List Nat) (take : Nat) :
    Nat.ofDigits radix (digits.map (take * ·)) =
      take * Nat.ofDigits radix digits := by
  induction digits with
  | nil => simp
  | cons digit digits ih =>
      simp [Nat.ofDigits_cons, ih]
      ring

end Challenge.Modexp.Reference.Proofs.Limbs
