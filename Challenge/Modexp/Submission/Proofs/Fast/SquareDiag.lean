import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# The diagonal product of one square row

`sq_row` computes the exact 512-bit product `a_i * (a_i + tb)` where
`tb = [a_{i-1} ≥ 2^255]` (`PUSH0 SGT`), even when `a_i + tb` wraps.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareDiag

open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

/-- `SGT 0 p` is the top bit of `p`. -/
theorem sgt_zero_toNat (p : UInt256) :
    (UInt256.sgt (UInt256.ofNat 0) p).toNat = p.toNat / 2 ^ 255 := by
  have hp : p.toNat < 2 ^ 256 := word_lt_size p
  unfold UInt256.sgt UInt256.toSignedNat
  have h0 : (UInt256.ofNat 0).toNat = 0 := by decide
  have hsz : UInt256.size = 2 ^ 256 := rfl
  simp only [h0, hsz]
  by_cases h : p.toNat < 2 ^ 256 / 2
  · rw [if_pos h, if_neg (by norm_num), Nat.div_eq_of_lt (by omega)]; decide
  · have h1 : p.toNat / 2 ^ 255 = 1 := by
      apply Nat.le_antisymm
      · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega))
      · exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    rw [if_neg h, if_pos (by push_cast; omega), h1]; decide

/-- The high word as `sq_row` computes it. -/
def diagHi (x f : UInt256) : UInt256 :=
  let w := UInt256.lt f x
  let lo := x * f
  let mm := UInt256.mulMod x f maxWord - w
  (mm - UInt256.lt mm lo) - lo

/-- Exactness of the diagonal: `hi * 2^256 + lo = x * (x + tb)` for `tb ≤ 1`,
with `f = x + tb` computed modulo `2^256`. -/
theorem diag_spec (x tb : UInt256) (htb : tb.toNat ≤ 1) :
    (diagHi x (x + tb)).toNat * 2 ^ 256 + (x * (x + tb)).toNat =
      x.toNat * (x.toNat + tb.toNat) := by
  have hx : x.toNat < 2 ^ 256 := word_lt_size x
  have hf := Challenge.EvmProof.Word.word_toNat_add x tb
  rcases Nat.lt_or_ge (x.toNat + tb.toNat) (2 ^ 256) with hnw | hw
  · -- no wrap: w = 0 and the high word is `mulHi x f`
    have hfv : (x + tb).toNat = x.toNat + tb.toNat := by rw [hf, Nat.mod_eq_of_lt hnw]
    have hw0 : UInt256.lt (x + tb) x = UInt256.ofNat 0 := by
      unfold UInt256.lt; rw [if_neg (by omega)]
    have hhi : diagHi x (x + tb) = mulHi x (x + tb) := by
      apply Challenge.EvmProof.Word.word_ext
      simp only [diagHi, mulHi, hw0]
      have hz : (UInt256.ofNat 0 : UInt256).toNat = 0 := by decide
      have hm := word_lt_size (UInt256.mulMod x (x + tb) maxWord)
      have hlo := word_lt_size (x * (x + tb))
      have hsub0 : UInt256.mulMod x (x + tb) maxWord - UInt256.ofNat 0 =
          UInt256.mulMod x (x + tb) maxWord := by
        apply Challenge.EvmProof.Word.word_ext
        rw [Challenge.EvmProof.Word.word_toNat_sub, hz]; omega
      rw [hsub0]
      have hc := word_lt_size (UInt256.lt (UInt256.mulMod x (x + tb) maxWord) (x * (x + tb)))
      have hc1 : (UInt256.lt (UInt256.mulMod x (x + tb) maxWord) (x * (x + tb))).toNat ≤ 1 := by
        rw [word_toNat_lt']; split <;> omega
      rw [Challenge.EvmProof.Word.word_toNat_sub, Challenge.EvmProof.Word.word_toNat_sub,
        Challenge.EvmProof.Word.word_toNat_sub, Challenge.EvmProof.Word.word_toNat_add]
      generalize (UInt256.mulMod x (x + tb) maxWord).toNat = M at *
      generalize (x * (x + tb)).toNat = L at *
      generalize (UInt256.lt (UInt256.mulMod x (x + tb) maxWord) (x * (x + tb))).toNat = C at *
      omega
    rw [hhi, mulHi_spec, hfv]
  · -- wrap: x = 2^256 - 1, tb = 1, f = 0
    have hx1 : x.toNat = 2 ^ 256 - 1 := by omega
    have ht1 : tb.toNat = 1 := by omega
    have hf0 : (x + tb).toNat = 0 := by rw [hf, hx1, ht1]; norm_num
    have hfz : x + tb = UInt256.ofNat 0 :=
      Challenge.EvmProof.Word.word_ext (by rw [hf0]; decide)
    rw [hfz]
    have hxm : x = UInt256.ofNat (2 ^ 256 - 1) :=
      Challenge.EvmProof.Word.word_ext (by rw [hx1]; decide)
    subst hxm
    rw [ht1]
    decide
end Challenge.Modexp.Submission.Proofs.Fast.SquareDiag
