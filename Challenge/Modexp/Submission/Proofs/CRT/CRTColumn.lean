import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace HistoricalSearch.CRTColumn

/-- Subtracting the known low word leaves the high-word contribution modulo P.
`H` may be an unreduced sum of residues. -/
theorem residualHigh (R P S H : Nat) (hP : 0 < P)
    (hH : H % P = S % P) :
    (H + P - (S % R) % P) % P = ((S / R) * (R % P)) % P := by
  haveI : NeZero P := ⟨hP.ne'⟩
  have hsub : (S % R) % P ≤ H + P := by
    have := Nat.mod_lt (S % R) hP
    omega
  have hH' : (H : ZMod P) = S :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hH
  have hlo : (((S % R) % P : Nat) : ZMod P) = (S % R : Nat) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.mod_modEq _ _)
  have hR' : ((R % P : Nat) : ZMod P) = R :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.mod_modEq _ _)
  have hdecomp : (S : ZMod P) = (S % R : Nat) + R * (S / R : Nat) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      congrArg (fun n : Nat => (n : ZMod P)) (Nat.mod_add_div S R).symm
  have hcalc : ((H + P - (S % R) % P : Nat) : ZMod P) =
      (((S / R) * (R % P) : Nat) : ZMod P) := by
    rw [Nat.cast_sub hsub, Nat.cast_add, ZMod.natCast_self, add_zero,
      hlo, hH', hdecomp, Nat.cast_mul, hR']
    ring
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hcalc

/-- When `R mod P` is small and the scaled quotient is below P, a division
replaces modular inversion entirely. -/
theorem reconstructHighWithoutInverse (R P K S H : Nat)
    (hP : 0 < P) (hK : 0 < K) (hRmod : R % P = K)
    (hH : H % P = S % P) (hbound : (S / R) * K < P) :
    ((H + P - (S % R) % P) % P) / K = S / R := by
  rw [residualHigh R P S H hP hH, hRmod, Nat.mod_eq_of_lt hbound]
  exact Nat.mul_div_cancel _ hK

/-- Recover the exact high word from a low word and a second residue.
The bound is essential: residues alone determine the sum only modulo `R * P`. -/
theorem reconstructHigh (R P I S H : Nat)
    (hR : 0 < R) (hP : 0 < P)
    (hbound : S < R * P)
    (hH : H % P = S % P)
    (hinv : (R * I) % P = 1 % P) :
    ((H + P - (S % R) % P) * I) % P = S / R := by
  haveI : NeZero P := ⟨hP.ne'⟩
  have hsub : (S % R) % P ≤ H + P := by
    have := Nat.mod_lt (S % R) hP
    omega
  have hI : (R : ZMod P) * I = 1 := by
    have hh : R * I ≡ 1 [MOD P] := hinv
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).2 hh
  have hH' : (H : ZMod P) = S :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hH
  have hlo : (((S % R) % P : Nat) : ZMod P) = (S % R : Nat) := by
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.mod_modEq _ _)
  have hdecomp : (S : ZMod P) = (S % R : Nat) + R * (S / R : Nat) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      congrArg (fun n : Nat => (n : ZMod P)) (Nat.mod_add_div S R).symm
  have hcalc : (((H + P - (S % R) % P) * I : Nat) : ZMod P) = (S / R : Nat) := by
    rw [Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_add, ZMod.natCast_self,
      add_zero, hlo, hH', hdecomp]
    calc (((S % R : Nat) : ZMod P) + R * (S / R : Nat) - (S % R : Nat)) * I
        = (S / R : Nat) * ((R : ZMod P) * I) := by ring
      _ = (S / R : Nat) := by rw [hI, mul_one]
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).1 hcalc
  change ((H + P - (S % R) % P) * I) % P = (S / R) % P at hmod
  have hq : S / R < P := (Nat.div_lt_iff_lt_mul hR).2 (by simpa [Nat.mul_comm] using hbound)
  exact hmod.trans (Nat.mod_eq_of_lt hq)

/-- Splitting first at `R = B*K`, then carrying at radix `B`, agrees with
direct division. In particular `B=2^248`, `K=2^8` bridges EVM words to limbs. -/
theorem carryFromHigh (B K S : Nat) (hB : 0 < B) :
    (S % (B * K)) / B + (S / (B * K)) * K = S / B := by
  have hd := Nat.mod_add_div S (B * K)
  have hdiv := congrArg (fun n : Nat => n / B) hd
  rw [show B * K * (S / (B * K)) = (S / (B * K)) * K * B by ring,
    Nat.add_mul_div_right _ _ hB] at hdiv
  exact hdiv

/-- A column containing at most n full products has a stable carry bound. -/
theorem columnCarryBound (B n S C : Nat) (hB : 0 < B)
    (hC : C ≤ n * (B - 1)) (hS : S ≤ n * (B - 1)^2 + C) :
    S / B ≤ n * (B - 1) := by
  have hB' : B - 1 + 1 = B := by omega
  have htotal : S ≤ n * (B - 1) * B := by
    calc S ≤ n * (B - 1)^2 + n * (B - 1) := by omega
      _ = n * (B - 1) * ((B - 1) + 1) := by ring
      _ = n * (B - 1) * B := by rw [hB']
  exact (Nat.div_le_div_right htotal).trans (by simp [hB.ne'])

def wordRadix : Nat := 2^256
def limbRadix : Nat := 2^248
def residueModulus : Nat := 2^251 - 1

theorem listSumBound (xs : List Nat) (M : Nat) (h : ∀ x ∈ xs, x ≤ M) :
    xs.sum ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have ht : ∀ x ∈ as, x ≤ M := by intro x hx; exact h x (by simp [hx])
    have hh := ih ht
    simp only [List.sum_cons, List.length_cons]
    nlinarith

theorem residueSum (xs : List Nat) (P : Nat) :
    (xs.map (fun x => x % P)).sum % P = xs.sum % P := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mod, Nat.mod_mod, ih]

/-- Supplies the reconstruction hypotheses from the actual list of column
products, including the carry's residue as the nineteenth term. -/
theorem columnListInvariant (xs : List Nat) (C : Nat)
    (hlen : xs.length ≤ 18)
    (hxs : ∀ x ∈ xs, x ≤ (limbRadix - 1)^2) :
    let S := xs.sum + C
    let H := (xs.map (fun x => x % residueModulus)).sum + C % residueModulus
    S ≤ 18 * (limbRadix - 1)^2 + C ∧
    H ≤ 19 * (residueModulus - 1) ∧
    H % residueModulus = S % residueModulus := by
  dsimp
  have hsum := listSumBound xs ((limbRadix - 1)^2) hxs
  have hs : xs.sum ≤ 18 * (limbRadix - 1)^2 :=
    hsum.trans (Nat.mul_le_mul_right _ hlen)
  have hp : 0 < residueModulus := by norm_num [residueModulus]
  have hm : ∀ x ∈ xs.map (fun x => x % residueModulus), x ≤ residueModulus - 1 := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    have := Nat.mod_lt y hp
    omega
  have hsumr := listSumBound (xs.map (fun x => x % residueModulus))
    (residueModulus - 1) hm
  simp only [List.length_map] at hsumr
  have hsr : (xs.map (fun x => x % residueModulus)).sum ≤ 18 * (residueModulus - 1) :=
    hsumr.trans (Nat.mul_le_mul_right _ hlen)
  have hc := Nat.mod_lt C hp
  refine ⟨by omega, by omega, ?_⟩
  simp only [Nat.add_mod, Nat.mod_mod, residueSum]

/-- Numeric conditions used by the nine-limb Montgomery kernel. Eighteen
products and a carry fit the exact-reconstruction domain; nineteen reduced
residue terms and the correcting P fit an EVM word without wraparound. -/
theorem kernel248Bounds (S C H : Nat)
    (hC : C ≤ 18 * (limbRadix - 1))
    (hS : S ≤ 18 * (limbRadix - 1)^2 + C)
    (hH : H ≤ 19 * (residueModulus - 1)) :
    S < wordRadix * residueModulus ∧
    (S / wordRadix) * 32 < residueModulus ∧
    H + residueModulus < wordRadix ∧
    S / limbRadix ≤ 18 * (limbRadix - 1) := by
  have hcarry := columnCarryBound limbRadix 18 S C (by norm_num [limbRadix]) hC hS
  norm_num [wordRadix, limbRadix, residueModulus] at *
  omega

/-- Complete numeric reconstruction used by the shift-only 248-bit kernel. -/
theorem kernel248Reconstruct (S C H : Nat)
    (hC : C ≤ 18 * (limbRadix - 1))
    (hS : S ≤ 18 * (limbRadix - 1)^2 + C)
    (hHbound : H ≤ 19 * (residueModulus - 1))
    (hH : H % residueModulus = S % residueModulus) :
    let lo := S % wordRadix
    let q := ((H + residueModulus - lo % residueModulus) % residueModulus) / 32
    q = S / wordRadix ∧ lo / limbRadix + q * 256 = S / limbRadix := by
  dsimp
  have hb := kernel248Bounds S C H hC hS hHbound
  have hq := reconstructHighWithoutInverse wordRadix residueModulus 32 S H
    (by norm_num [residueModulus]) (by decide)
    (by norm_num [wordRadix, residueModulus]) hH hb.2.1
  refine ⟨hq, ?_⟩
  rw [hq]
  have hr : wordRadix = limbRadix * 256 := by norm_num [wordRadix, limbRadix]
  rw [hr]
  exact carryFromHigh limbRadix 256 S (by norm_num [limbRadix])

/-- The concrete wrap/shift arithmetic used by the EVM reconstruction.
This is an arithmetic bridge; it does not assert execution of a bytecode body. -/
theorem kernel248WrappedShifts (S C H : Nat)
    (hC : C ≤ 18 * (limbRadix - 1))
    (hS : S ≤ 18 * (limbRadix - 1)^2 + C)
    (hHbound : H ≤ 19 * (residueModulus - 1))
    (hH : H % residueModulus = S % residueModulus) :
    let lo := S % wordRadix
    let x := (H + (residueModulus - lo % residueModulus)) % wordRadix
    let q := (x % residueModulus) >>> 5
    ((lo >>> 248) + ((q <<< 8) % wordRadix)) % wordRadix = S / limbRadix := by
  dsimp
  have hb := kernel248Bounds S C H hC hS hHbound
  have hl := Nat.mod_lt (S % wordRadix) (show 0 < residueModulus by norm_num [residueModulus])
  have heq : H + (residueModulus - (S % wordRadix) % residueModulus) =
      H + residueModulus - (S % wordRadix) % residueModulus := by omega
  have hx : H + (residueModulus - (S % wordRadix) % residueModulus) < wordRadix := by
    omega
  rw [Nat.mod_eq_of_lt hx, heq]
  have hr := kernel248Reconstruct S C H hC hS hHbound hH
  dsimp at hr
  have hsplit : (S % wordRadix) / limbRadix + S / wordRadix * 256 = S / limbRadix := by
    simpa only [hr.1] using hr.2
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num only [show 2^5 = (32 : Nat) by norm_num, show 2^8 = (256 : Nat) by norm_num]
  rw [hr.1]
  have hcarrylt : S / limbRadix < wordRadix := by
    have := hb.2.2.2
    norm_num [wordRadix, limbRadix] at *
    omega
  have hq8 : S / wordRadix * 256 < wordRadix := by
    calc S / wordRadix * 256 ≤ (S % wordRadix) / limbRadix + S / wordRadix * 256 :=
        Nat.le_add_left _ _
      _ = S / limbRadix := hsplit
      _ < wordRadix := hcarrylt
  rw [Nat.mod_eq_of_lt hq8]
  change ((S % wordRadix) / limbRadix + S / wordRadix * 256) % wordRadix = _
  rw [hsplit, Nat.mod_eq_of_lt hcarrylt]

#print axioms reconstructHigh
#print axioms carryFromHigh
#print axioms residualHigh
#print axioms reconstructHighWithoutInverse
#print axioms columnCarryBound
#print axioms kernel248Bounds
#print axioms kernel248Reconstruct
#print axioms columnListInvariant
#print axioms kernel248WrappedShifts

end HistoricalSearch.CRTColumn
