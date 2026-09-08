import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Mathlib.Data.Nat.Bits

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Two-lane mask decomposition

This module isolates the natural-number identity used by the packed RIPEMD
lane invariant.  Bits `0..31` form the low lane and bits `64..95` form the
high lane; masking drops every other bit.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask

/-- The 32-bit window of `p` starting at bit `k`. -/
def windowN (p k : Nat) : Nat := (p >>> k) % 2 ^ 32

/-- The low packed lane, at bits `0..31`. -/
def lane0N (p : Nat) : Nat := windowN p 0

/-- The high packed lane, at bits `64..95`. -/
def lane1N (p : Nat) : Nat := windowN p 64

def maskLN : Nat := 2 ^ 32 - 1
def maskRN : Nat := (2 ^ 32 - 1) * 2 ^ 64
def maskLRN : Nat := maskLN + maskRN

@[simp] theorem windowN_lt (p k : Nat) : windowN p k < 2 ^ 32 :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

@[simp] theorem testBit_windowN (p k i : Nat) :
    (windowN p k).testBit i = (decide (i < 32) && p.testBit (k + i)) := by
  rw [windowN, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem testBit_maskLN (i : Nat) : maskLN.testBit i = decide (i < 32) := by
  simpa [maskLN] using Nat.testBit_two_pow_sub_one 32 i

theorem testBit_maskRN (i : Nat) :
    maskRN.testBit i = (decide (64 ≤ i) && decide (i - 64 < 32)) := by
  have hshift : maskRN = (2 ^ 32 - 1) <<< 64 := by
    simp [maskRN, Nat.shiftLeft_eq]
  rw [hshift, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem maskLRN_or : maskLRN = maskRN ||| maskLN := by
  have hlow : maskLN < 2 ^ 64 := by
    simp [maskLN]
  have hshift : maskRN = (2 ^ 32 - 1) <<< 64 := by
    simp [maskRN, Nat.shiftLeft_eq]
  rw [maskLRN, Nat.add_comm, hshift]
  exact Nat.shiftLeft_add_eq_or_of_lt hlow (2 ^ 32 - 1)

theorem testBit_maskLRN (i : Nat) :
    maskLRN.testBit i =
      (decide (i < 32) || (decide (64 ≤ i) && decide (i - 64 < 32))) := by
  rw [maskLRN_or, Nat.testBit_or, testBit_maskRN, testBit_maskLN]
  exact Bool.or_comm _ _

private theorem lanes_add_eq_or (p : Nat) :
    lane0N p + lane1N p * 2 ^ 64 = (lane1N p <<< 64) ||| lane0N p := by
  have hlow : lane0N p < 2 ^ 64 := by
    exact lt_trans (windowN_lt p 0) (by omega)
  have hshift : lane1N p * 2 ^ 64 = lane1N p <<< 64 := by
    simp [Nat.shiftLeft_eq]
  rw [Nat.add_comm, hshift]
  exact Nat.shiftLeft_add_eq_or_of_lt hlow (lane1N p)

/-- Masking keeps exactly the two 32-bit lanes and clears every gap bit. -/
theorem and_maskLR_split (p : Nat) :
    p &&& maskLRN = lane0N p + lane1N p * 2 ^ 64 := by
  rw [lanes_add_eq_or]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_maskLRN, Nat.testBit_or,
    Nat.testBit_shiftLeft]
  by_cases hlow : i < 32
  · have hnotHigh : ¬64 ≤ i := by omega
    simp [lane0N, lane1N, testBit_windowN, hlow, hnotHigh]
  · by_cases hhigh : 64 ≤ i
    · by_cases hwindow : i - 64 < 32
      · simp [lane0N, lane1N, testBit_windowN, hlow, hhigh, hwindow,
          Nat.add_sub_of_le hhigh]
      · simp [lane0N, lane1N, testBit_windowN, hlow, hhigh, hwindow]
    · simp [lane0N, lane1N, testBit_windowN, hlow, hhigh]

#print axioms and_maskLR_split

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
