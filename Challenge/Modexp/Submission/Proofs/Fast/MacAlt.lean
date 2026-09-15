import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Reassociated multiply-accumulate

These identities originate in @ercumentyildirim's submission
`a257dd1c-b071-47af-8650-199607537d32`.

The limb bodies form the three-way sum `t + x*y + c` as `(x*y + c) + t` rather
than as `c + (t + x*y)`.  The stored word is the same by commutativity of
addition; the two carry bits differ individually, but their sum is the same,
because both count the overflow of the same three-way sum.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.MacAlt

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.EvmProof.Word

theorem mulMod_comm (a b : UInt256) :
    UInt256.mulMod b a maxWord = UInt256.mulMod a b maxWord := by
  apply word_ext
  rw [word_toNat_mulMod_max, word_toNat_mulMod_max, Nat.mul_comm]

theorem macSumNat (x y t c : UInt256) :
    (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = (c.toNat + (t.toNat + (x * y).toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  congr 1
  omega

/-- Wrapping subtraction reassociates: `a - (b - d) - e = a + (d - (e + b))`. -/
theorem subSubFold (a b d e : UInt256) :
    a - (b - d) - e = a + (d - (e + b)) := by
  apply word_ext
  have ha := word_lt_size a
  have hb := word_lt_size b
  have hd := word_lt_size d
  have he := word_lt_size e
  simp only [word_toNat_sub, word_toNat_add]
  omega

/-- The two carry bits of the reassociated sum add up to the same total. -/
theorem carryPair (x y t c : UInt256) :
    (if (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
       then 1 else 0) +
      (if ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < c.toNat then 1 else 0) =
    (UInt256.lt (c + (t + x * y)) c).toNat + (UInt256.lt (t + x * y) t).toNat := by
  have ha : (x * y).toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size (x * y); norm_num at h; exact h
  have hc : c.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size c; norm_num at h; exact h
  have ht : t.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size t; norm_num at h; exact h
  simp only [word_toNat_lt', word_toNat_add,
    show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by norm_num]
  obtain ⟨q1, r1, hq1, hr1, he1⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ (x * y).toNat + c.toNat = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨((x * y).toNat + c.toNat) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936,
      by omega, by omega, by omega⟩
  obtain ⟨q2, r2, hq2, hr2, he2⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ t.toNat + (x * y).toNat = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨(t.toNat + (x * y).toNat) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, (t.toNat + (x * y).toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936,
      by omega, by omega, by omega⟩
  obtain ⟨q3, r3, hq3, hr3, he3⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ t.toNat + r1 = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨(t.toNat + r1) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, (t.toNat + r1) % 115792089237316195423570985008687907853269984665640564039457584007913129639936, by omega, by omega, by omega⟩
  obtain ⟨q4, r4, hq4, hr4, he4⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ c.toNat + r2 = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨(c.toNat + r2) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, (c.toNat + r2) % 115792089237316195423570985008687907853269984665640564039457584007913129639936, by omega, by omega, by omega⟩
  have m1 : ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r1 := by omega
  have m2 : (t.toNat + (x * y).toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r2 := by omega
  have m3 : (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r3 := by omega
  have m4 : (c.toNat + r2) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r4 := by omega
  rw [m1, m2, m3, m4]
  split_ifs <;> omega


theorem ifBit_toNat (P : Prop) [Decidable P] :
    (if P then (UInt256.ofNat 1) else UInt256.ofNat 0).toNat = if P then 1 else 0 := by
  split <;> simp

theorem bit_le (P : Prop) [Decidable P] : (if P then 1 else 0) ≤ 1 := by
  split <;> simp

/-- The carry the reassociated body computes is `macCarry`. -/
theorem macCarryFix (x y t c : UInt256) :
    (if (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 then
        (UInt256.ofNat 1) else UInt256.ofNat 0) +
      (((if ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < c.toNat then (UInt256.ofNat 1)
            else UInt256.ofNat 0) -
          (UInt256.lt (UInt256.mulMod y x maxWord) (x * y) - UInt256.mulMod y x maxWord)) -
        x * y) =
      UInt256.lt (c + (t + x * y)) c + (UInt256.lt (t + x * y) t + mulHi x y) := by
  rw [mulMod_comm, subSubFold]
  have hp := carryPair x y t c
  have hH : (mulHi x y).toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size (mulHi x y); norm_num at h; exact h
  have hb1 := bit_le ((t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)
  have hb2 := bit_le (((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < c.toNat)
  apply word_ext
  simp only [word_toNat_add, ifBit_toNat, word_toNat_lt', mulHi,
    show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by norm_num] at hp ⊢
  omega

end Challenge.Modexp.Submission.Proofs.Fast.MacAlt
