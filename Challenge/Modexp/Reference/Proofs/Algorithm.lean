import Challenge.Modexp.Spec
import Challenge.EvmProof.Memory
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import YulEvmCompiler.BytesLemmas
set_option warningAsError true
/-!
# Mathematical MODEXP facts

This file contains bytecode-independent arithmetic used by both execution
paths.  In particular, it proves the pinned precompile implementation's
tail-recursive `modPow` definition agrees with ordinary exponentiation modulo
the modulus; the EVM loop proofs can therefore target a small algebraic
invariant instead of the implementation recursion.
-/

namespace Challenge.Modexp.Reference.Proofs.Algorithm

open EvmSemantics
open EvmSemantics.EVM

theorem modPowAux_mod (base acc modulus e : Nat) :
    Precompile.modPowAux base acc modulus e % modulus =
      (acc * base ^ e) % modulus := by
  induction e using Nat.strong_induction_on generalizing base acc with
  | _ e ih =>
    unfold Precompile.modPowAux
    split
    · next h => subst h; simp
    · next h =>
      have hlt : e / 2 < e := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      rw [ih (e / 2) hlt]
      have hpow : base ^ e = (base * base) ^ (e / 2) * base ^ (e % 2) := by
        rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]
        congr 1
        omega
      rw [hpow]
      rcases Nat.mod_two_eq_zero_or_one e with hpar | hpar
      · rw [if_neg (by omega), hpar, Nat.pow_zero, Nat.mul_one,
          Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]
      · rw [if_pos hpar, hpar, Nat.pow_one,
          Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]
        rw [Nat.mul_assoc, Nat.mul_comm base ((base * base) ^ (e / 2))]

theorem modPowAux_lt {base acc modulus e : Nat} (hmodulus : 0 < modulus)
    (hacc : acc < modulus) :
    Precompile.modPowAux base acc modulus e < modulus := by
  induction e using Nat.strong_induction_on generalizing base acc with
  | _ e ih =>
    unfold Precompile.modPowAux
    split
    · exact hacc
    · next h =>
      apply ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))
      split
      · exact Nat.mod_lt _ hmodulus
      · exact hacc

/-- The executable precompile definition is ordinary modular
exponentiation.  This also records the EIP-198 zero-modulus convention. -/
theorem modPow_eq (base exponent modulus : Nat) :
    Precompile.modPow base exponent modulus =
      if modulus = 0 then 0 else base ^ exponent % modulus := by
  unfold Precompile.modPow
  split
  · rfl
  · next hm0 =>
    split
    · next hm1 =>
      subst modulus
      exact (Nat.mod_one _).symm
    · next hm1 =>
      have hmpos : 0 < modulus := Nat.pos_of_ne_zero hm0
      have hone : 1 < modulus := by omega
      have hlt := modPowAux_lt (base := base % modulus) (e := exponent)
        hmpos hone
      calc
        Precompile.modPowAux (base % modulus) 1 modulus exponent =
            Precompile.modPowAux (base % modulus) 1 modulus exponent % modulus :=
          (Nat.mod_eq_of_lt hlt).symm
        _ = (1 * (base % modulus) ^ exponent) % modulus :=
          modPowAux_mod _ _ _ _
        _ = (base % modulus) ^ exponent % modulus := by rw [Nat.one_mul]
        _ = base ^ exponent % modulus := (Nat.pow_mod _ _ _).symm

theorem modPow_lt {base exponent modulus : Nat} (hmodulus : 0 < modulus) :
    Precompile.modPow base exponent modulus < modulus := by
  rw [modPow_eq, if_neg (Nat.ne_of_gt hmodulus)]
  exact Nat.mod_lt _ hmodulus

/-! ## Constant-shape double-and-add multiplication -/

/-- Process an LSB-first list of selector bits.  The first component is the
accumulated product and the second is the repeatedly doubled addend. -/
def mulBits (modulus : Nat) : Nat → Nat → List Nat → Nat × Nat
  | acc, addend, [] => (acc, addend)
  | acc, addend, bit :: bits =>
      mulBits modulus ((acc + bit * addend) % modulus)
        ((addend + addend) % modulus) bits

theorem mulBits_fst (modulus acc addend : Nat) (bits : List Nat) :
    (mulBits modulus acc addend bits).1 % modulus =
      (acc + addend * Nat.ofDigits 2 bits) % modulus := by
  induction bits generalizing acc addend with
  | nil => simp [mulBits]
  | cons bit bits ih =>
      rw [mulBits, ih]
      simp only [Nat.ofDigits_cons]
      have hacc := Nat.mod_modEq (acc + bit * addend) modulus
      have haddend := Nat.mod_modEq (addend + addend) modulus
      have hcongr := hacc.add (haddend.mul_right (Nat.ofDigits 2 bits))
      have heq : (acc + bit * addend) +
          (addend + addend) * Nat.ofDigits 2 bits =
        acc + addend * (bit + 2 * Nat.ofDigits 2 bits) := by ring
      rw [heq] at hcongr
      exact hcongr

theorem mulBits_snd (modulus acc addend : Nat) (bits : List Nat) :
    (mulBits modulus acc addend bits).2 % modulus =
      (addend * 2 ^ bits.length) % modulus := by
  induction bits generalizing acc addend with
  | nil => simp [mulBits]
  | cons bit bits ih =>
      rw [mulBits, ih]
      have haddend := Nat.mod_modEq (addend + addend) modulus
      have hcongr := haddend.mul_right (2 ^ bits.length)
      have heq : (addend + addend) * 2 ^ bits.length =
          addend * 2 ^ (bit :: bits).length := by
        simp only [List.length_cons, pow_succ]
        ring
      rw [heq] at hcongr
      exact hcongr

theorem zeroBytes (offset width : Nat) :
    MachineState.readPadded ByteArray.empty offset width =
      Precompile.natToBytes 0 width := by
  unfold Precompile.natToBytes
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hleft hright
    have hiwidth : i < width := by
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] at hright
      exact hright
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos (by simpa using hleft),
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
        0 width i hiwidth]
    simp

end Challenge.Modexp.Reference.Proofs.Algorithm
