import Challenge.Modexp.Submission.Proofs.Cycle.DoubleInput

set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
Biased recovery with an arbitrary common extra-residue aggregate. Keeping the
aggregate explicit lets late columns reuse the double-input rewrite without
fixing the number of square/quotient residues in the column.
-/
namespace CycleSubmission.DoubleInput
open EvmSemantics Challenge.EvmProof.Word

/-- Shared-input doubling preserves biased recovery when the common aggregate
leaves room for two product residues and the bias. -/
theorem high_double_biased_extra (a b p h digit factor : UInt256)
    (hp : 0 < p.toNat) (ha : a.toNat+a.toNat < 2^256)
    (hd : digit.toNat < p.toNat)
    (hroom : 3*p.toNat+h.toNat ≤ 2^256) :
    UInt256.mulMod factor (p + ((h+UInt256.mulMod b (a+a) p)-digit)) p =
      UInt256.mulMod factor
        (p + ((h+(UInt256.mulMod b a p+UInt256.mulMod b a p))-digit)) p := by
  have residue_lt (x y : UInt256) : (UInt256.mulMod x y p).toNat < p.toNat := by
    rw [mulMod_nat _ _ _ hp]
    exact Nat.mod_lt _ hp
  have add_le (x y : UInt256) : (x+y).toNat ≤ x.toNat+y.toNat := by
    rw [word_toNat_add]
    exact Nat.mod_le _ _
  have hnew : (UInt256.mulMod b (a+a) p+h).toNat+p.toNat < 2^256 := by
    have h0 := add_le (UInt256.mulMod b (a+a) p) h
    have hm := residue_lt b (a+a)
    omega
  have hold : (UInt256.mulMod b a p+UInt256.mulMod b a p+h).toNat+
      p.toNat < 2^256 := by
    have h0 := add_le (UInt256.mulMod b a p) (UInt256.mulMod b a p)
    have h1 := add_le (UInt256.mulMod b a p+UInt256.mulMod b a p) h
    have hm := residue_lt b a
    omega
  have he := congrArg UInt256.toNat
    (high_double a b p h (UInt256.ofNat 1) hp ha (by omega))
  have hone : (UInt256.ofNat 1).toNat = 1 := by norm_num [word_toNat_ofNat]
  simp only [mulMod_nat _ _ _ hp, hone, Nat.one_mul] at he
  simpa only [word_add_comm h (UInt256.mulMod b (a+a) p),
    word_add_comm h (UInt256.mulMod b a p+UInt256.mulMod b a p)] using
    (biased_congruent _ _ digit p factor hp hd hnew hold he)

#print axioms high_double_biased_extra
end CycleSubmission.DoubleInput
