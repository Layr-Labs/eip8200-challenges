import Challenge.Modexp.Submission.Proofs.CRT.CRTColumn
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace HistoricalSearch.GenericColumn
open HistoricalSearch.CRTColumn

/-- All widths at most 248 share the same exact CRT reconstruction bound. -/
theorem widthBounds (W S C H : Nat) (hW : W ≤ 248)
    (hC : C ≤ 18 * (2^W - 1)) (hS : S ≤ 18 * (2^W - 1)^2 + C)
    (hH : H ≤ 19 * (residueModulus - 1)) :
    S < wordRadix * residueModulus ∧
    (S / wordRadix) * 32 < residueModulus ∧
    H + residueModulus < wordRadix ∧
    S / 2^W ≤ 18 * (2^W - 1) := by
  have hp : 2^W ≤ limbRadix := Nat.pow_le_pow_right (by decide) hW
  have hd : 2^W - 1 ≤ limbRadix - 1 := Nat.sub_le_sub_right hp 1
  have hc : C ≤ 18*(limbRadix-1) := hC.trans (Nat.mul_le_mul_left 18 hd)
  have hs : S ≤ 18*(limbRadix-1)^2+C := by nlinarith
  have hb := kernel248Bounds S C H hc hs hH
  exact ⟨hb.1, hb.2.1, hb.2.2.1,
    columnCarryBound (2^W) 18 S C (Nat.two_pow_pos W) hC hS⟩

theorem reconstructAtWidth (W S C H : Nat) (hW : W ≤ 248)
    (hC : C ≤ 18 * (2^W - 1)) (hS : S ≤ 18 * (2^W - 1)^2 + C)
    (hHbound : H ≤ 19 * (residueModulus - 1))
    (hH : H % residueModulus = S % residueModulus) :
    let lo := S % wordRadix
    let q := ((H + residueModulus - lo % residueModulus) % residueModulus) / 32
    q = S / wordRadix ∧ lo / 2^W + q * 2^(256-W) = S / 2^W := by
  dsimp
  have hb := widthBounds W S C H hW hC hS hHbound
  have hq := reconstructHighWithoutInverse wordRadix residueModulus 32 S H
    (by norm_num [residueModulus]) (by decide)
    (by norm_num [wordRadix, residueModulus]) hH hb.2.1
  refine ⟨hq, ?_⟩
  rw [hq]
  have hr : wordRadix = 2^W * 2^(256-W) := by
    rw [wordRadix, ← Nat.pow_add, Nat.add_sub_of_le (by omega : W ≤ 256)]
  rw [hr]
  exact carryFromHigh (2^W) (2^(256-W)) S (Nat.two_pow_pos W)

/-- Widths at most 246 permit injecting the carry directly into the residue
accumulator. Its reduction modulo P is provably redundant. -/
theorem carryReductionRedundant (W C : Nat) (hW : W ≤ 246)
    (hC : C ≤ 18*(2^W-1)) : C < residueModulus ∧ C % residueModulus = C := by
  have hp : 2^W ≤ (2^246 : Nat) := Nat.pow_le_pow_right (by decide) hW
  have hc : C < residueModulus := by
    norm_num [residueModulus] at *
    omega
  exact ⟨hc, Nat.mod_eq_of_lt hc⟩

theorem columnListInvariantAtWidth (W : Nat) (xs : List Nat) (C : Nat)
    (hlen : xs.length ≤ 18) (hxs : ∀ x ∈ xs, x ≤ (2^W-1)^2) :
    let S := xs.sum+C
    let H := (xs.map (fun x => x % residueModulus)).sum+C % residueModulus
    S ≤ 18*(2^W-1)^2+C ∧ H ≤ 19*(residueModulus-1) ∧
      H % residueModulus = S % residueModulus := by
  dsimp
  have hsum := listSumBound xs ((2^W-1)^2) hxs
  have hs := hsum.trans (Nat.mul_le_mul_right ((2^W-1)^2) hlen)
  have hp : 0 < residueModulus := by norm_num [residueModulus]
  have hm : ∀ x ∈ xs.map (fun x => x % residueModulus), x ≤ residueModulus-1 := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    have := Nat.mod_lt y hp
    omega
  have hsumr := listSumBound (xs.map (fun x => x % residueModulus)) (residueModulus-1) hm
  simp only [List.length_map] at hsumr
  have hsr := hsumr.trans (Nat.mul_le_mul_right (residueModulus-1) hlen)
  have hc := Nat.mod_lt C hp
  refine ⟨by omega, by omega, ?_⟩
  simp only [Nat.add_mod, Nat.mod_mod, residueSum]

/-- Width-independent proof of the actual wrapping and shift operations. -/
theorem wrappedShiftsAtWidth (W S C H : Nat) (hW : W ≤ 248)
    (hC : C ≤ 18*(2^W-1)) (hS : S ≤ 18*(2^W-1)^2+C)
    (hHbound : H ≤ 19*(residueModulus-1))
    (hH : H % residueModulus = S % residueModulus) :
    let lo := S % wordRadix
    let x := (H+(residueModulus-lo % residueModulus)) % wordRadix
    let q := (x % residueModulus) >>> 5
    ((lo >>> W)+((q <<< (256-W)) % wordRadix)) % wordRadix = S/2^W := by
  dsimp
  have hb := widthBounds W S C H hW hC hS hHbound
  have hl := Nat.mod_lt (S % wordRadix) (show 0 < residueModulus by norm_num [residueModulus])
  have heq : H+(residueModulus-(S % wordRadix) % residueModulus) =
      H+residueModulus-(S % wordRadix) % residueModulus := by omega
  have hx : H+(residueModulus-(S % wordRadix) % residueModulus) < wordRadix := by omega
  rw [Nat.mod_eq_of_lt hx, heq]
  have hr := reconstructAtWidth W S C H hW hC hS hHbound hH
  dsimp at hr
  have hsplit : (S % wordRadix)/2^W + S/wordRadix*2^(256-W) = S/2^W := by
    simpa only [hr.1] using hr.2
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num only [show 2^5 = (32 : Nat) by norm_num]
  rw [hr.1]
  have hpow : 2^W ≤ (2^248 : Nat) := Nat.pow_le_pow_right (by decide) hW
  have hcarrylt : S/2^W < wordRadix := by
    have := hb.2.2.2
    norm_num [wordRadix] at *
    omega
  have hqshift : S/wordRadix*2^(256-W) < wordRadix := by
    calc S/wordRadix*2^(256-W) ≤ (S % wordRadix)/2^W+S/wordRadix*2^(256-W) := Nat.le_add_left _ _
      _ = S/2^W := hsplit
      _ < wordRadix := hcarrylt
  rw [Nat.mod_eq_of_lt hqshift, hsplit, Nat.mod_eq_of_lt hcarrylt]

theorem width244TopCellBound :
    2*((2^96 : Nat)-1)^2+4*((2^96 : Nat)-1)+18 < 2^244 := by norm_num

#print axioms widthBounds
#print axioms reconstructAtWidth
#print axioms carryReductionRedundant
#print axioms columnListInvariantAtWidth
#print axioms wrappedShiftsAtWidth
#print axioms width244TopCellBound

end HistoricalSearch.GenericColumn
