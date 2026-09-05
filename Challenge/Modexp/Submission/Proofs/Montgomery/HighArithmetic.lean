import Challenge.EvmProof.Word
import Mathlib.Tactic

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Montgomery.HighArithmetic

def B : Nat := 2 ^ 256

private theorem B_pos : 0 < B := by norm_num [B]
private theorem B_pred_pos : 0 < B - 1 := by norm_num [B]

/-- The base-B high limb can be reconstructed from reduction modulo B-1. -/
theorem quotient_relation (p : Nat) (hp : p ≤ (B - 1) * (B - 1)) :
    let lo := p % B
    let hi := p / B
    let mm := p % (B - 1)
    if mm < lo then hi = mm + B - 1 - lo else hi = mm - lo := by
  let lo := p % B
  let hi := p / B
  let mm := p % (B - 1)
  let q := p / (B - 1)
  have hlo : lo < B := Nat.mod_lt _ B_pos
  have hmm : mm < B - 1 := Nat.mod_lt _ B_pred_pos
  have hB := Nat.mod_add_div p B
  have hM := Nat.mod_add_div p (B - 1)
  have hhi : hi ≤ B - 2 := by
    dsimp only [hi, B]
    rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2 ^ 256)]
    dsimp only [B] at hp
    omega
  have hq : q ≤ B - 1 := by
    dsimp only [q, B]
    rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2 ^ 256 - 1)]
    dsimp only [B] at hp
    omega
  dsimp only [lo, hi, mm, q] at hlo hmm hB hM hhi hq ⊢
  simp only [B] at hlo hmm hB hM hhi hq ⊢
  split <;> omega

/-- Natural-number model of one EVM `SUB`. -/
def subWord (a b : Nat) : Nat := (a + B - b) % B

/-- The exact `MUL; MULMOD (B-1); SUB; LT; SUB` high-half formula. -/
def highViaMulMod (p : Nat) : Nat :=
  let lo := p % B
  let mm := p % (B - 1)
  subWord (subWord mm lo) (if mm < lo then 1 else 0)

theorem highViaMulMod_eq (p : Nat) (hp : p ≤ (B - 1) * (B - 1)) :
    highViaMulMod p = p / B := by
  have hrel := quotient_relation p hp
  have hhi : p / B ≤ B - 2 := by
    rw [Nat.div_le_iff_le_mul B_pos]
    dsimp only [B] at hp ⊢
    omega
  have hlo : p % B < B := Nat.mod_lt _ B_pos
  have hBtwo : 2 ≤ B := by norm_num [B]
  simp only [highViaMulMod, subWord]
  by_cases hlt : p % (B - 1) < p % B
  · rw [if_pos hlt]
    rw [if_pos hlt] at hrel
    have hfirst : p % (B - 1) + B - p % B = p / B + 1 := by
      omega
    have hfirstmod : (p % (B - 1) + B - p % B) % B = p / B + 1 := by
      rw [hfirst, Nat.mod_eq_of_lt]
      omega
    rw [hfirstmod]
    have hsecond : p / B + 1 + B - 1 = B + p / B := by omega
    rw [hsecond]
    simp [Nat.mod_eq_of_lt (by omega : p / B < B)]
  · rw [if_neg hlt]
    rw [if_neg hlt] at hrel
    have hfirst : p % (B - 1) + B - p % B = B + p / B := by
      omega
    have hfirstmod : (p % (B - 1) + B - p % B) % B = p / B := by
      rw [hfirst]
      simp [Nat.mod_eq_of_lt (by omega : p / B < B)]
    rw [hfirstmod]
    simp [Nat.mod_eq_of_lt (by omega : p / B < B)]

open EvmSemantics

private theorem word_toNat_mul (x y : UInt256) :
    (x * y).toNat = (x.toNat * y.toNat) % B := by
  change (x.val * y.val).val = _
  rw [Fin.val_mul]
  rfl

def maxWord : UInt256 := UInt256.ofNat (B - 1)

@[simp] theorem maxWord_toNat : maxWord.toNat = B - 1 := by
  rw [maxWord, Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  norm_num [B]

private theorem mulMod_max_toNat (x y : UInt256) :
    (UInt256.mulMod x y maxWord).toNat =
      (x.toNat * y.toNat) % (B - 1) := by
  unfold UInt256.mulMod
  rw [if_neg]
  · rw [Challenge.EvmProof.Word.word_toNat_ofNat, maxWord_toNat]
    apply Nat.mod_eq_of_lt
    exact (Nat.mod_lt _ B_pred_pos).trans (by norm_num [B])
  · change maxWord.toNat ≠ 0
    norm_num [B]

def fullHighWord (x y : UInt256) : UInt256 :=
  let lo := x * y
  let mm := UInt256.mulMod x y maxWord
  mm - lo - UInt256.lt mm lo

/-- The actual EVM expression returns the high 256 bits of the product. -/
theorem fullHighWord_toNat (x y : UInt256) :
    (fullHighWord x y).toNat = (x.toNat * y.toNat) / B := by
  have hx : x.toNat ≤ B - 1 := by
    change x.toNat ≤ 2 ^ 256 - 1
    exact Nat.le_pred_of_lt x.val.isLt
  have hy : y.toNat ≤ B - 1 := by
    change y.toNat ≤ 2 ^ 256 - 1
    exact Nat.le_pred_of_lt y.val.isLt
  have hp : x.toNat * y.toNat ≤ (B - 1) * (B - 1) :=
    Nat.mul_le_mul hx hy
  unfold fullHighWord
  rw [Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_lt, word_toNat_mul,
    mulMod_max_toNat]
  simpa [highViaMulMod, subWord, B, Nat.add_comm] using
    (highViaMulMod_eq (x.toNat * y.toNat) hp)

end Challenge.Modexp.Submission.Proofs.Montgomery.HighArithmetic
