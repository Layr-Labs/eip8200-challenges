import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
import EvmSemantics.Machine.MachineState

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLoadModel

open EvmSemantics
open Challenge.EvmProof.Word
open PackedLaneMask

/-- A post-spread memory relation, not an assumption that arbitrary memory
is zero. The concrete preprocessing trace must establish both read shapes,
including the last right load's bytes beyond the final spread store. -/
structure SpreadReads (memory : ByteArray) (words : Nat → UInt32) : Prop where
  left : ∀ i, i < 16 → ∃ high : Nat,
    (MachineState.readWord memory (16 * i)).toNat =
      (words i).toNat ||| high <<< 128
  right : ∀ i, i < 16 → ∃ high : Nat,
    (MachineState.readWord memory (16 * i + 8)).toNat =
      (words i).toNat <<< 64 ||| high <<< 128

def loadPair (memory : ByteArray) (i j : Nat) : UInt256 :=
  UInt256.lor (MachineState.readWord memory (16 * i))
    (MachineState.readWord memory (16 * j + 8))

private theorem word_bit_high (w : UInt32) (i : Nat) (hi : ¬i < 32) :
    w.toNat.testBit i = false := by
  have hm : w.toNat % 2 ^ 32 = w.toNat := Nat.mod_eq_of_lt w.toNat_lt
  have hb := congrArg (fun n : Nat => n.testBit i) hm
  simp only [Nat.testBit_mod_two_pow, hi, decide_false, Bool.false_and] at hb
  exact hb.symm

private theorem pair_slot0 (l r : UInt32) (a b : Nat) :
    ((l.toNat ||| a <<< 128) ||| (r.toNat <<< 64 ||| b <<< 128)) % 2 ^ 64 =
      l.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · have h128 : ¬128 ≤ i := by omega
    have h64 : ¬64 ≤ i := by omega
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft,
      hi, h128, h64, decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.or_false]
  · have h32 : ¬i < 32 := by omega
    simp only [Nat.testBit_mod_two_pow, hi, decide_false, Bool.false_and,
      word_bit_high l i h32]

private theorem pair_lane1 (l r : UInt32) (a b : Nat) :
    lane1N ((l.toNat ||| a <<< 128) ||| (r.toNat <<< 64 ||| b <<< 128)) =
      r.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · have h128 : ¬128 ≤ 64 + i := by omega
    have h64 : 64 ≤ 64 + i := by omega
    have h32 : ¬64 + i < 32 := by omega
    simp [lane1N, testBit_windowN, Nat.testBit_or, Nat.testBit_shiftLeft,
      hi, h128, h64, word_bit_high l (64 + i) h32]
  · simp [lane1N, testBit_windowN, hi, word_bit_high r i hi]

/-- The paired machine loads have the requested lanes and no low-slot junk.
This is conditional on SpreadReads; it does not certify the spreading stores. -/
theorem loadPair_spec (memory : ByteArray) (words : Nat → UInt32)
    (h : SpreadReads memory words) (i j : Nat) (hi : i < 16) (hj : j < 16) :
    lane0N (loadPair memory i j).toNat = (words i).toNat ∧
    lane1N (loadPair memory i j).toNat = (words j).toNat ∧
    (loadPair memory i j).toNat % 2 ^ 64 < 2 ^ 32 := by
  obtain ⟨a, ha⟩ := h.left i hi
  obtain ⟨b, hb⟩ := h.right j hj
  have hraw : (loadPair memory i j).toNat =
      ((words i).toNat ||| a <<< 128) ||| ((words j).toNat <<< 64 ||| b <<< 128) := by
    rw [loadPair, word_toNat_lor, ha, hb]
  have hslot := pair_slot0 (words i) (words j) a b
  rw [hraw]
  refine ⟨?_, pair_lane1 _ _ _ _, ?_⟩
  · have hdiv : 2 ^ 32 ∣ (2 : Nat) ^ 64 := by norm_num
    simp only [lane0N, windowN, Nat.shiftRight_zero]
    rw [← Nat.mod_mod_of_dvd _ hdiv, hslot, Nat.mod_eq_of_lt (words i).toNat_lt]
  · rw [hslot]
    exact (words i).toNat_lt

#print axioms loadPair_spec

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLoadModel
