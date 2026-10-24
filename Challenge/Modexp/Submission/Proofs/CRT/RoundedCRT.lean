import Challenge.Modexp.Submission.Proofs.CRT.CRTWordBridge
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace HistoricalSearch.RoundedCRT
open HistoricalSearch.CRTColumn HistoricalSearch.GenericColumn

/-- The complemented low word adds a known rounding bias to the high residue. -/
theorem roundedResidual (R P K S H : Nat) (hR : 0 < R) (_hP : 0 < P)
    (hK : 0 < K) (hRmod : R % P = K) (hH : H % P = S % P) :
    (H + (R - 1 - S % R)) % P = ((S / R + 1) * K - 1) % P := by
  haveI : NeZero P := ⟨_hP.ne'⟩
  have hlo := Nat.mod_lt S hR
  have hsub : S % R ≤ R - 1 := by omega
  have hk : 1 ≤ (S / R + 1) * K := Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) hK)
  have hHv : (H : ZMod P) = S := (ZMod.natCast_eq_natCast_iff _ _ _).2 hH
  have hKv : (K : ZMod P) = R := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    change K % P = R % P
    rw [← hRmod, Nat.mod_mod]
  have hd : (S : ZMod P) = (S % R : Nat) + R * (S / R : Nat) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      congrArg (fun n : Nat => (n : ZMod P)) (Nat.mod_add_div S R).symm
  apply (ZMod.natCast_eq_natCast_iff _ _ _).1
  rw [Nat.cast_add, Nat.cast_sub hsub, Nat.cast_sub (by omega : 1 ≤ R),
    Nat.cast_one, hHv, hd, Nat.cast_sub hk, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, hKv]
  ring

/-- A later division discards the entire rounding bias, avoiding a separate
reduction of the low word and a correcting subtraction. -/
theorem roundedHigh (R P K S H : Nat) (hR : 0 < R) (hP : 0 < P)
    (hK : 0 < K) (hRmod : R % P = K) (hH : H % P = S % P)
    (hbound : (S / R + 1) * K - 1 < P) :
    ((H + (R - 1 - S % R)) % P) / K = S / R := by
  rw [roundedResidual R P K S H hR hP hK hRmod hH, Nat.mod_eq_of_lt hbound]
  have heq : (S / R + 1) * K - 1 = (K - 1) + (S / R) * K := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [heq, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt (by omega : K - 1 < K),
    Nat.zero_add]

theorem roundedWidthBound (W S C : Nat) (hW : W ≤ 248)
    (hC : C ≤ 18 * (2^W - 1)) (hS : S ≤ 18 * (2^W - 1)^2 + C) :
    (S / wordRadix + 1) * 32 - 1 < residueModulus := by
  have hp : 2^W ≤ (2^248 : Nat) := Nat.pow_le_pow_right (by decide) hW
  have hb : S ≤ 18 * ((2^248 : Nat)-1)^2 + 18*((2^248 : Nat)-1) := by
    nlinarith [Nat.sub_le_sub_right hp 1]
  norm_num [wordRadix, residueModulus] at *
  omega

end HistoricalSearch.RoundedCRT
