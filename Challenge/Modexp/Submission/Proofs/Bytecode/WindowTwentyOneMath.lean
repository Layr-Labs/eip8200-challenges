import Challenge.Modexp.Submission.Proofs.Bytecode.WindowMath

set_option warningAsError true

/-!
# Artifact-independent arithmetic for a twenty-one-nibble window body

The exponent is one 256-bit word. Its first nibble initializes the table
accumulator; three bodies consume twenty-one further nibbles each. The arithmetic
does not assume a base width, and the same result supports both the full-word
and positive short-base parsers. No execution or artifact theorem is asserted
in this module.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMath

open EvmSemantics
open EvmSemantics.EVM

def exponentPrefix (exponent count : Nat) : Nat :=
  exponent / 16 ^ (64 - count)

def nibble (exponent index : Nat) : Nat :=
  exponent / 16 ^ (63 - index) % 16

theorem nibble_lt (exponent index : Nat) : nibble exponent index < 16 :=
  Nat.mod_lt _ (by decide)

theorem prefix_succ (exponent index : Nat) (hindex : index < 64) :
    exponentPrefix exponent (index + 1) =
      exponentPrefix exponent index * 16 + nibble exponent index := by
  unfold exponentPrefix nibble
  rw [show 64 - (index + 1) = 63 - index by omega,
    show 64 - index = (63 - index) + 1 by omega, Nat.pow_succ,
    ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod' (exponent / 16 ^ (63 - index)) 16).symm

theorem nibble_zero_eq_prefix (exponent : Nat) (hexponent : exponent < 16 ^ 64) :
    nibble exponent 0 = exponentPrefix exponent 1 := by
  change exponent / 16 ^ 63 % 16 = exponent / 16 ^ 63
  apply Nat.mod_eq_of_lt
  apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (16 : Nat) ^ 63)).2
  simpa [Nat.pow_succ, Nat.mul_comm] using hexponent

/-- A four-square/table step preserves the modular exponent prefix even when
the incoming table entry is the deliberately unreduced slot zero or one. -/
theorem nibbleWordStep_mod_pow (base modulus acc : UInt256)
    (exponent digit : Nat) (hmodulus : 0 < modulus.toNat)
    (hacc : acc.toNat % modulus.toNat = base.toNat ^ exponent % modulus.toNat) :
    (WindowMath.nibbleWordStep modulus base acc digit).toNat % modulus.toNat =
      base.toNat ^ (exponent * 16 + digit) % modulus.toNat := by
  rw [WindowMath.nibbleWordStep_toNat _ _ _ _ hmodulus,
    WindowMath.nibbleStep, Nat.mod_mod]
  calc
    (acc.toNat ^ 16 * base.toNat ^ digit) % modulus.toNat =
        ((acc.toNat ^ 16 % modulus.toNat) *
          (base.toNat ^ digit % modulus.toNat)) % modulus.toNat :=
      Nat.mul_mod _ _ _
    _ = (((acc.toNat % modulus.toNat) ^ 16 % modulus.toNat) *
          (base.toNat ^ digit % modulus.toNat)) % modulus.toNat := by
      rw [Nat.pow_mod acc.toNat]
    _ = (((base.toNat ^ exponent % modulus.toNat) ^ 16 % modulus.toNat) *
          (base.toNat ^ digit % modulus.toNat)) % modulus.toNat := by rw [hacc]
    _ = (((base.toNat ^ exponent) ^ 16 % modulus.toNat) *
          (base.toNat ^ digit % modulus.toNat)) % modulus.toNat := by
      rw [← Nat.pow_mod]
    _ = ((base.toNat ^ exponent) ^ 16 * base.toNat ^ digit) % modulus.toNat :=
      (Nat.mul_mod _ _ _).symm
    _ = base.toNat ^ (exponent * 16 + digit) % modulus.toNat := by
      rw [← Nat.pow_mul, ← Nat.pow_add]

/-- Consume `count` exponent nibbles starting at `start`, in execution order. -/
def advance (base modulus : UInt256) (exponent start : Nat) :
    Nat → UInt256 → UInt256
  | 0, acc => acc
  | count + 1, acc => WindowMath.nibbleWordStep modulus base
      (advance base modulus exponent start count acc) (nibble exponent (start + count))

theorem advance_add (base modulus : UInt256)
    (exponent start left right : Nat) (acc : UInt256) :
    advance base modulus exponent start (left + right) acc =
      advance base modulus exponent (start + left) right
        (advance base modulus exponent start left acc) := by
  induction right with
  | zero => rfl
  | succ right ih =>
      rw [Nat.add_succ, advance, ih, advance]
      congr 2
      omega

def initialAccumulator (base modulus : UInt256) (exponent : Nat) : UInt256 :=
  WindowMath.tableWord base modulus (nibble exponent 0)

def accumulator (base modulus : UInt256) (exponent count : Nat) : UInt256 :=
  advance base modulus exponent 1 count (initialAccumulator base modulus exponent)

theorem accumulator_mod (base modulus : UInt256) (exponent count : Nat)
    (hmodulus : 0 < modulus.toNat) (hexponent : exponent < 16 ^ 64)
    (hcount : count ≤ 63) :
    (accumulator base modulus exponent count).toNat % modulus.toNat =
      base.toNat ^ exponentPrefix exponent (count + 1) % modulus.toNat := by
  revert hcount
  induction count with
  | zero =>
      intro _
      simpa [accumulator, advance, initialAccumulator,
        nibble_zero_eq_prefix exponent hexponent] using
        WindowMath.tableWord_mod base modulus (nibble exponent 0) hmodulus
  | succ count ih =>
      intro hcount
      have hprev := ih (by omega)
      change (WindowMath.nibbleWordStep modulus base
        (accumulator base modulus exponent count)
        (nibble exponent (1 + count))).toNat % modulus.toNat = _
      rw [nibbleWordStep_mod_pow base modulus _ _ _ hmodulus hprev]
      rw [show 1 + count = count + 1 by omega,
        ← prefix_succ exponent (count + 1) (by omega)]

theorem accumulator_twentyOne (base modulus : UInt256) (exponent count : Nat) :
    accumulator base modulus exponent (count + 21) =
      advance base modulus exponent (1 + count) 21
        (accumulator base modulus exponent count) := by
  exact advance_add base modulus exponent 1 count 21 _

/-- First nibble plus three twenty-one-nibble bodies is the full exponent word. -/
theorem three_bodies_toNat (base modulus : UInt256) (exponent : Nat)
    (hmodulus : 0 < modulus.toNat) (hexponent : exponent < 16 ^ 64) :
    (accumulator base modulus exponent (3 * 21)).toNat =
      base.toNat ^ exponent % modulus.toNat := by
  have hlt : (accumulator base modulus exponent 63).toNat < modulus.toNat := by
    change (WindowMath.nibbleWordStep modulus base
      (accumulator base modulus exponent 62) (nibble exponent 63)).toNat < _
    rw [WindowMath.nibbleWordStep_toNat _ _ _ _ hmodulus, WindowMath.nibbleStep]
    exact Nat.mod_lt _ hmodulus
  have h := accumulator_mod base modulus exponent 63 hmodulus hexponent (by decide)
  rw [Nat.mod_eq_of_lt hlt] at h
  simpa [exponentPrefix] using h

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMath
