import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000

/-!
# UInt256 glue for the packed RIPEMD lanes

This module transports the proved two-lane `Nat` mask decomposition to EVM
words and records the exact inter-step bounds.  Rotation multiplication and
window correctness deliberately live elsewhere.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant

open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask

def maskL : UInt256 := UInt256.ofNat maskLN
def maskR : UInt256 := UInt256.ofNat maskRN
def maskLR : UInt256 := UInt256.ofNat maskLRN

private theorem maskLN_lt : maskLN < 2 ^ 256 := by
  unfold maskLN
  norm_num

private theorem maskRN_lt : maskRN < 2 ^ 256 := by
  unfold maskRN
  norm_num [← Nat.pow_add]

private theorem maskLRN_lt : maskLRN < 2 ^ 256 := by
  unfold maskLRN maskLN maskRN
  norm_num [← Nat.pow_add]

@[simp] theorem maskL_toNat : maskL.toNat = maskLN := by
  rw [maskL, word_toNat_ofNat]
  exact Nat.mod_eq_of_lt maskLN_lt

@[simp] theorem maskR_toNat : maskR.toNat = maskRN := by
  rw [maskR, word_toNat_ofNat]
  exact Nat.mod_eq_of_lt maskRN_lt

@[simp] theorem maskLR_toNat : maskLR.toNat = maskLRN := by
  rw [maskLR, word_toNat_ofNat]
  exact Nat.mod_eq_of_lt maskLRN_lt

/-- Inter-step bound: each 64-bit slot has a 32-bit lane and one carry bit. -/
structure Inv (P : UInt256) : Prop where
  low : P.toNat % 2 ^ 64 < 2 ^ 33
  high : P.toNat / 2 ^ 64 < 2 ^ 33

/-- Strong inter-step bound for values freshly masked to the two lanes. -/
structure Clean (P : UInt256) : Prop where
  low : P.toNat % 2 ^ 64 < 2 ^ 32
  high : P.toNat / 2 ^ 64 < 2 ^ 32

theorem Clean.toInv {P : UInt256} (h : Clean P) : Inv P :=
  ⟨lt_trans h.low (by norm_num), lt_trans h.high (by norm_num)⟩

/-- The full word identity behind every masked multiplication input.  In
particular, it rules out hidden gap bits rather than merely bounding the two
projected windows. -/
theorem masked_word_split (P : UInt256) :
    (P &&& maskLR).toNat =
      lane0N P.toNat + lane1N P.toNat * 2 ^ 64 := by
  change (UInt256.land P maskLR).toNat = _
  rw [word_toNat_land, maskLR_toNat, and_maskLR_split]

/-- Masking an arbitrary word leaves exactly two clean 32-bit lanes. -/
theorem masked_input_clean (P : UInt256) : Clean (P &&& maskLR) := by
  constructor
  · rw [masked_word_split]
    have h0 : lane0N P.toNat < 2 ^ 32 := windowN_lt _ _
    have hmod :
        (lane0N P.toNat + lane1N P.toNat * 2 ^ 64) % 2 ^ 64 =
          lane0N P.toNat := by
      rw [Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (lt_trans h0 (by norm_num))
    rw [hmod]
    exact h0
  · rw [masked_word_split]
    have h0 : lane0N P.toNat < 2 ^ 32 := windowN_lt _ _
    have h1 : lane1N P.toNat < 2 ^ 32 := windowN_lt _ _
    rw [Nat.mul_comm (lane1N P.toNat) (2 ^ 64),
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (lt_trans h0 (by norm_num)), Nat.zero_add]
    exact h1

/-- Compatibility name used by the packed-step development. -/
theorem clean_and_maskLR (P : UInt256) : Clean (P &&& maskLR) :=
  masked_input_clean P

theorem masked_input_low (P : UInt256) :
    (P &&& maskLR).toNat % 2 ^ 64 < 2 ^ 32 :=
  (masked_input_clean P).low

theorem masked_input_high (P : UInt256) :
    (P &&& maskLR).toNat / 2 ^ 64 < 2 ^ 32 :=
  (masked_input_clean P).high

private theorem lane0N_and_maskLRN (p : Nat) :
    lane0N (p &&& maskLRN) = lane0N p := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lane0N, testBit_windowN]
  by_cases hi : i < 32
  · have hi64 : ¬64 ≤ i := by omega
    simp [Nat.testBit_and, testBit_maskLRN, hi, hi64]
  · simp [hi]

private theorem lane1N_and_maskLRN (p : Nat) :
    lane1N (p &&& maskLRN) = lane1N p := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lane1N, testBit_windowN]
  by_cases hi : i < 32
  · have h64 : 64 ≤ 64 + i := by omega
    have hsub : 64 + i - 64 = i := by omega
    have hnotlow : ¬64 + i < 32 := by omega
    simp [Nat.testBit_and, testBit_maskLRN, hi, h64, hsub, hnotlow]
  · simp [hi]

theorem lane0_and_maskLR (P : UInt256) :
    lane0N (P &&& maskLR).toNat = lane0N P.toNat := by
  change lane0N (UInt256.land P maskLR).toNat = _
  rw [word_toNat_land, maskLR_toNat, lane0N_and_maskLRN]

theorem lane1_and_maskLR (P : UInt256) :
    lane1N (P &&& maskLR).toNat = lane1N P.toNat := by
  change lane1N (UInt256.land P maskLR).toNat = _
  rw [word_toNat_land, maskLR_toNat, lane1N_and_maskLRN]

/-- Each projected lane of a masked multiplication input is 32-bit.  The
strong no-gap premise used to justify the whole-word multiplication is
`masked_word_split` (or equivalently `masked_input_clean`). -/
theorem mul_precondition (P : UInt256) :
    lane0N (P &&& maskLR).toNat < 2 ^ 32 ∧
      lane1N (P &&& maskLR).toNat < 2 ^ 32 :=
  ⟨windowN_lt _ _, windowN_lt _ _⟩

private theorem slot_add (a b : Nat)
    (hlo : a % 2 ^ 64 + b % 2 ^ 64 < 2 ^ 64) :
    (a + b) % 2 ^ 64 = a % 2 ^ 64 + b % 2 ^ 64 ∧
      (a + b) / 2 ^ 64 = a / 2 ^ 64 + b / 2 ^ 64 := by
  have ha := Nat.div_add_mod a (2 ^ 64)
  have hb := Nat.div_add_mod b (2 ^ 64)
  have hab := Nat.div_add_mod (a + b) (2 ^ 64)
  have hma : a % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hmb : b % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hmab : (a + b) % 2 ^ 64 < 2 ^ 64 :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  omega

/-- Adding two clean packed words produces an inter-step word.  Both the
slot-0 no-carry fact and the absence of UInt256 wrap are derived here from
`Clean`; callers do not carry extra arithmetic side conditions. -/
theorem inv_of_rot_add (rot e : UInt256)
    (hrot : Clean rot) (he : Clean e) : Inv (rot + e) := by
  have hnc : rot.toNat % 2 ^ 64 + e.toNat % 2 ^ 64 < 2 ^ 64 := by
    calc
      rot.toNat % 2 ^ 64 + e.toNat % 2 ^ 64 < 2 ^ 32 + 2 ^ 32 :=
        Nat.add_lt_add hrot.low he.low
      _ = 2 ^ 33 := by norm_num
      _ < 2 ^ 64 := by norm_num
  have hrotBound : rot.toNat < 2 ^ 32 * 2 ^ 64 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)).mp hrot.high
  have heBound : e.toNat < 2 ^ 32 * 2 ^ 64 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)).mp he.high
  have hfit : rot.toNat + e.toNat < 2 ^ 256 := by
    calc
      rot.toNat + e.toNat <
          2 ^ 32 * 2 ^ 64 + 2 ^ 32 * 2 ^ 64 :=
        Nat.add_lt_add hrotBound heBound
      _ < 2 ^ 256 := by norm_num [← Nat.pow_add]
  have hsum : (rot + e).toNat = rot.toNat + e.toNat := by
    rw [word_toNat_add]
    exact Nat.mod_eq_of_lt hfit
  have hslot := slot_add rot.toNat e.toNat hnc
  constructor
  · rw [hsum, hslot.1]
    exact lt_of_lt_of_le
      (Nat.add_lt_add hrot.low he.low) (by norm_num)
  · rw [hsum, hslot.2]
    exact lt_of_lt_of_le
      (Nat.add_lt_add hrot.high he.high) (by norm_num)

#print axioms masked_word_split
#print axioms masked_input_clean
#print axioms inv_of_rot_add

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant
