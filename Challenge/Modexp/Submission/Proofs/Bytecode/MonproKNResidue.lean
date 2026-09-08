import Challenge.EvmProof.Word

set_option warningAsError true

/-!
Artifact-independent residue arithmetic shared by the two eight-copy MONPRO loops.
L1 supplies remaining = n-j; L2 supplies remaining = n-1-k.  No bytecode or
subroutine correctness theorem is imported or asserted here.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNResidue

open EvmSemantics

def residue (remaining : Nat) : Nat := (8 - remaining % 8) % 8

theorem residue_lt (remaining : Nat) : residue remaining < 8 :=
  Nat.mod_lt _ (by decide)

/-- The first suffix is nonempty, fits, and leaves a multiple of eight. -/
theorem suffix_bounds (remaining : Nat) (hpositive : 0 < remaining) :
    0 < 8 - residue remaining ∧ 8 - residue remaining ≤ remaining ∧
      (remaining - (8 - residue remaining)) % 8 = 0 := by
  have hr := Nat.mod_lt remaining (show 0 < 8 by decide)
  unfold residue
  omega

theorem shifted_borrow (remaining : Nat)
    (hpositive : 0 < remaining) (hbound : remaining ≤ 32) :
    (UInt256.shiftRight (UInt256.ofNat (2 ^ 256 - 32 * remaining))
      (UInt256.ofNat 5)).toNat = 2 ^ 251 - remaining := by
  have hsmall : 32 * remaining ≤ 1024 := by omega
  have hfit : 2 ^ 256 - 32 * remaining < 2 ^ 256 := by omega
  have hlarge : remaining ≤ 2 ^ 251 := by
    have : (32 : Nat) ≤ 2 ^ 251 := by norm_num
    omega
  have hscale : 2 ^ 256 - 32 * remaining = 32 * (2 ^ 251 - remaining) := by
    have : (2 : Nat) ^ 256 = 32 * 2 ^ 251 := by norm_num
    omega
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by decide),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit,
    Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 5 = 32 by decide,
    hscale, Nat.mul_div_cancel_left _ (by decide)]

/-- Wrapped negative 32-byte gaps select the correct first copy, for all widths. -/
theorem masked_borrow (remaining : Nat)
    (hpositive : 0 < remaining) (hbound : remaining ≤ 32) :
    UInt256.land (UInt256.ofNat 7)
      (UInt256.shiftRight (UInt256.ofNat (2 ^ 256 - 32 * remaining))
        (UInt256.ofNat 5)) = UInt256.ofNat (residue remaining) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, shifted_borrow remaining hpositive hbound,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    show 7 % 2 ^ 256 = 7 by norm_num, Nat.and_comm,
    show (7 : Nat) = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  have hmod : (2 ^ 251 - remaining) % 2 ^ 3 = residue remaining := by
    have hpower : (2 : Nat) ^ 251 = 8 * 2 ^ 248 := by norm_num
    have hlarge : remaining ≤ 2 ^ 251 := by
      have : (32 : Nat) ≤ 2 ^ 251 := by norm_num
      omega
    unfold residue
    omega
  rw [hmod, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (residue_lt remaining) (by norm_num))).symm

/-- The concrete dispatchers need only establish their ordinary pointer gap. -/
theorem dispatch_value (low high remaining : Nat)
    (hpositive : 0 < remaining) (hbound : remaining ≤ 32)
    (hlow : low < 2 ^ 256) (hhigh : high < 2 ^ 256)
    (hgap : high = low + 32 * remaining) :
    UInt256.land (UInt256.ofNat 7)
      (UInt256.shiftRight (UInt256.ofNat low - UInt256.ofNat high)
        (UInt256.ofNat 5)) = UInt256.ofNat (residue remaining) := by
  have hsub : UInt256.ofNat low - UInt256.ofNat high =
      UInt256.ofNat (2 ^ 256 - 32 * remaining) := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_sub]
    simp only [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hlow, Nat.mod_eq_of_lt hhigh]
    congr 1
    omega
  rw [hsub]
  exact masked_borrow remaining hpositive hbound

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNResidue
