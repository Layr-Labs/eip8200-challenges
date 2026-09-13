import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerBoolean
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactInput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRoundSemantic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRound
open Paired144Core Paired144Boolean
open PairedLaneRoundSemantic (scalarSum)

def rawSum (mode : Nat) (a b c d message k : BitVec 256) : BitVec 256 :=
  (((a + StaggerBoolean.raw mode pairMask (StaggerBoolean.selector mode) b c d) + message) +
    StaggerBoolean.key mode pairMask k)

theorem rawSum_canonical (mode : Nat) (hm : mode < 9)
    (a : BitVec 256) (bl br cl cr dl dr : BitVec 32) (message k : BitVec 256) :
    rawSum mode a (pack bl br) (pack cl cr) (pack dl dr) message k =
      (((a + StaggerBoolean.canonical mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr)) + message) + k) := by
  have hb := StaggerBoolean.raw_add_key mode hm pairMask (StaggerBoolean.selector mode)
    (pack bl br) (pack cl cr) (pack dl dr) k (StaggerBoolean.selector_supported mode)
    (StaggerBoolean.pack_supported _ _) (StaggerBoolean.pack_supported _ _) (StaggerBoolean.pack_supported _ _)
  unfold rawSum
  calc
    ((a + StaggerBoolean.raw mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr)) + message) + StaggerBoolean.key mode pairMask k =
      (a + message) + (StaggerBoolean.raw mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr) + StaggerBoolean.key mode pairMask k) := by ac_rfl
    _ = (a + message) + (StaggerBoolean.canonical mode pairMask (StaggerBoolean.selector mode)
        (pack bl br) (pack cl cr) (pack dl dr) + k) := by rw [hb]
    _ = _ := by ac_rfl

theorem rawSum_pack (mode : Nat) (hm : mode < 9)
    (al ar bl br cl cr dl dr wl wr kl kr : BitVec 32) (message : BitVec 256)
    (hmsg : message = pack wl wr) :
    rawSum mode (pack al ar) (pack bl br) (pack cl cr) (pack dl dr) message (pack kl kr) =
      (((pack al ar + pack (f (StaggerBoolean.leftGroup mode) (BitVec.allOnes 32) bl cl dl)
        (f (StaggerBoolean.rightGroup mode) (BitVec.allOnes 32) br cr dr)) + pack wl wr) + pack kl kr) := by
  rw [rawSum_canonical mode hm, hmsg, StaggerBoolean.canonical_pack mode hm]

theorem rawSum_inputs (mode : Nat) (hm : mode < 9)
    (al ar bl br cl cr dl dr wl wr kl kr : BitVec 32) (message : BitVec 256)
    (hmsg : message = pack wl wr) :
    let x := rawSum mode (pack al ar) (pack bl br) (pack cl cr) (pack dl dr) message (pack kl kr)
    let a := scalarSum (StaggerBoolean.leftGroup mode) al bl cl dl wl kl
    let b := scalarSum (StaggerBoolean.rightGroup mode) ar br cr dr wr kr
    Paired144CompactInput.compact x = BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< 72) ∧
      normalize x = pack a b := by
  dsimp only
  rw [rawSum_pack mode hm _ _ _ _ _ _ _ _ _ _ _ _ message hmsg]
  constructor
  · exact Paired144CompactInput.compact_four_adds _ _ _ _ _ _ _ _
  · exact Paired144CompactInput.normalize_four_adds _ _ _ _ _ _ _ _

/-! ## Dead high bits in a message word

Two schedule words reach the table without their 32-bit mask.  A message word then carries
extra bits above each lane, `jl` in bits `[32,144)` and `jr` in bits `[176,256)`.  The lane
sum never carries across bit 144, and the two rotation paths read only the lane bits
(`normalize`) or the bits below 104 of each half (`compact`), so the extra bits are dead. -/

def junk (jl jr : Nat) : BitVec 256 := BitVec.ofNat 256 (jl * 2 ^ 32 + jr * 2 ^ 176)

theorem rawSum_junk (mode : Nat) (a b c d message k J : BitVec 256) :
    rawSum mode a b c d (message + J) k = rawSum mode a b c d message k + J := by
  unfold rawSum
  ac_rfl

theorem four_adds_ofNat (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) :
    (((pack a0 b0+pack a1 b1)+pack a2 b2)+pack a3 b3) =
      BitVec.ofNat 256 ((a0.toNat+a1.toNat+a2.toNat+a3.toNat) +
        (b0.toNat+b1.toNat+b2.toNat+b3.toNat) * 2 ^ 144) := by
  rw [Paired144CompactInput.four_adds_wide, Paired144CompactInput.wide_ofNat]
  · have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
    simp only [Nat.reducePow] at *; omega
  · have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
    simp only [Nat.reducePow] at *; omega

theorem ofNat_add_junk (A B jl jr : Nat) :
    BitVec.ofNat 256 (A + B * 2 ^ 144) + junk jl jr =
      BitVec.ofNat 256 ((A + jl * 2 ^ 32) + (B + jr * 2 ^ 32) * 2 ^ 144) := by
  unfold junk
  rw [BitVec.ofNat_add_ofNat]
  refine congrArg (BitVec.ofNat 256) ?_
  rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]
  omega

theorem split_lt (X Y : Nat) (hX : X < 2 ^ 144) (hY : Y < 2 ^ 112) :
    X + Y * 2 ^ 144 < 2 ^ 256 := by
  have h1 : X + Y * 2 ^ 144 < (Y + 1) * 2 ^ 144 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    exact Nat.add_lt_add_left hX _
  have h2 : (Y + 1) * 2 ^ 144 ≤ 2 ^ 112 * 2 ^ 144 := Nat.mul_le_mul_right _ hY
  rw [← Nat.pow_add] at h2
  exact Nat.lt_of_lt_of_le h1 h2

theorem normalize_ofNat_junk (A B jl jr : Nat)
    (hA : A + jl * 2 ^ 32 < 2 ^ 144) (hB : B + jr * 2 ^ 32 < 2 ^ 112) :
    normalize (BitVec.ofNat 256 (A + B * 2 ^ 144) + junk jl jr) =
      normalize (BitVec.ofNat 256 (A + B * 2 ^ 144)) := by
  rw [ofNat_add_junk]
  have hA' : A < 2 ^ 144 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hA
  have hB' : B < 2 ^ 112 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hB
  have hN := split_lt A B hA' hB'
  have hN' := split_lt _ _ hA hB
  have h1 : low (BitVec.ofNat 256 ((A + jl * 2 ^ 32) + (B + jr * 2 ^ 32) * 2 ^ 144)) =
      low (BitVec.ofNat 256 (A + B * 2 ^ 144)) := by
    apply BitVec.eq_of_toNat_eq
    unfold low
    rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_zero, Nat.shiftRight_zero, Nat.mod_eq_of_lt hN', Nat.mod_eq_of_lt hN]
    have e1 : (A + jl * 2 ^ 32) + (B + jr * 2 ^ 32) * 2 ^ 144 =
        A + (jl + (B + jr * 2 ^ 32) * 2 ^ 112) * 2 ^ 32 := by ring
    have e2 : A + B * 2 ^ 144 = A + (B * 2 ^ 112) * 2 ^ 32 := by ring
    rw [e1, e2, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]
  have h2 : high (BitVec.ofNat 256 ((A + jl * 2 ^ 32) + (B + jr * 2 ^ 32) * 2 ^ 144)) =
      high (BitVec.ofNat 256 (A + B * 2 ^ 144)) := by
    apply BitVec.eq_of_toNat_eq
    unfold high
    rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hN', Nat.mod_eq_of_lt hN,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos 144), Nat.add_mul_div_right _ _ (Nat.two_pow_pos 144),
      Nat.div_eq_of_lt hA, Nat.div_eq_of_lt hA', Nat.zero_add, Nat.zero_add,
      Nat.add_mul_mod_self_right]
  unfold normalize
  rw [h1, h2]

/-- `Paired144CompactInput.wide` with a 112-bit upper half: `compact` still only sees the
low 32 bits of each half. -/
def wideH (a : BitVec 72) (b : BitVec 112) : BitVec 256 := b ++ a.setWidth 144

theorem compact_wideH (a : BitVec 72) (b : BitVec 112) :
    Paired144CompactInput.compact (wideH a b) =
      Paired144CompactInput.small (a.setWidth 32) (b.setWidth 32) := by
  have hmask : BitVec.ofNat 256 ((2^32-1)*(1+2^72)) =
      Paired144CompactInput.small (BitVec.allOnes 32) (BitVec.allOnes 32) := by decide
  unfold Paired144CompactInput.compact
  rw [hmask]
  unfold wideH Paired144CompactInput.small
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    Nat.add_comm 72 i, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  by_cases h32 : i < 32
  · have h72 : i < 72 := by omega
    have h144 : i < 144 := by omega
    have hsum : i+72 <144 := by omega
    have hsum256 : i+72 <256 := by omega
    have hz := BitVec.getLsbD_of_ge a (i+72) (show 72 ≤ i+72 by omega)
    simp only [Bool.or_false, ite_false, h32,h72,h144,hsum,hsum256,if_pos,decide_true, Bool.true_and, Bool.and_true, hz, Bool.or_false]
  · by_cases h72 : i < 72
    · simp only [ite_false, h72,h32,if_pos,decide_false,Bool.false_and,Bool.and_false,ite_false]
    · by_cases h104 : i <104
      · have h144 : i<144 := by omega
        have hsum : ¬i+72<144 := by omega
        have hs32 : i-72<32 := by omega
        have h112 : i-72<112 := by omega
        have hs184 : i-72<184 := by omega
        have hs256 : i+72<256 := by omega
        have heq : i+72-144=i-72 := by omega
        have hz := BitVec.getLsbD_of_ge a i (show 72 ≤ i by omega)
        simp only [ite_false, h72,h144,hsum,h112,hs32,hs184,hs256,heq,if_pos,if_neg,
          decide_true,Bool.true_and,Bool.and_true,hz,Bool.false_or]
      · have hs32 : ¬i-72<32 := by omega
        simp only [ite_false, h72,hs32,if_neg,decide_false,Bool.false_and,Bool.and_false,ite_false]

theorem wideH_toNat (a : BitVec 72) (b : BitVec 112) :
    (wideH a b).toNat = a.toNat + b.toNat * 2 ^ 144 := by
  unfold wideH
  rw [BitVec.toNat_append, BitVec.toNat_setWidth_of_le (by decide)]
  have ha : a.toNat < 2 ^ 144 := Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) (by decide))
  rw [← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

theorem wideH_ofNat (a b : Nat) (ha : a < 2 ^ 72) (hb : b < 2 ^ 112) :
    wideH (BitVec.ofNat 72 a) (BitVec.ofNat 112 b) = BitVec.ofNat 256 (a + b * 2 ^ 144) := by
  apply BitVec.eq_of_toNat_eq
  rw [wideH_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (split_lt a b
    (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by decide))) hb)).symm

theorem compact_ofNat_junk (A B jl jr : Nat)
    (hA : A + jl * 2 ^ 32 < 2 ^ 72) (hB : B + jr * 2 ^ 32 < 2 ^ 112) :
    Paired144CompactInput.compact (BitVec.ofNat 256 (A + B * 2 ^ 144) + junk jl jr) =
      Paired144CompactInput.compact (BitVec.ofNat 256 (A + B * 2 ^ 144)) := by
  rw [ofNat_add_junk,
    ← wideH_ofNat _ _ hA hB, ← wideH_ofNat A B (by omega) (by omega),
    compact_wideH, compact_wideH]
  simp only [BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 72),
    BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 112)]
  have h1 : BitVec.ofNat 32 (A + jl * 2 ^ 32) = BitVec.ofNat 32 A := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    omega
  have h2 : BitVec.ofNat 32 (B + jr * 2 ^ 32) = BitVec.ofNat 32 B := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    omega
  rw [h1, h2]

theorem rawSum_inputs_junk (mode : Nat) (hm : mode < 9)
    (al ar bl br cl cr dl dr wl wr kl kr : BitVec 32) (jl jr : Nat)
    (hjl : jl < 2 ^ 64) (hjr : jr < 2 ^ 64) :
    let x := rawSum mode (pack al ar) (pack bl br) (pack cl cr) (pack dl dr)
      (pack wl wr + junk jl jr) (pack kl kr)
    let a := scalarSum (StaggerBoolean.leftGroup mode) al bl cl dl wl kl
    let b := scalarSum (StaggerBoolean.rightGroup mode) ar br cr dr wr kr
    (jl < 2 ^ 35 →
      Paired144CompactInput.compact x = BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< 72)) ∧
      normalize x = pack a b := by
  dsimp only
  have h := rawSum_inputs mode hm al ar bl br cl cr dl dr wl wr kl kr (pack wl wr) rfl
  dsimp only at h
  rw [rawSum_junk]
  rw [rawSum_pack mode hm _ _ _ _ _ _ _ _ _ _ _ _ (pack wl wr) rfl] at h ⊢
  rw [four_adds_ofNat] at h ⊢
  have hsum : ∀ x y z w : BitVec 32, x.toNat + y.toNat + z.toNat + w.toNat < 2 ^ 34 := by
    intro x y z w
    have := x.isLt; have := y.isLt; have := z.isLt; have := w.isLt
    simp only [Nat.reducePow] at *; omega
  refine ⟨fun h32l => ?_, ?_⟩
  · rw [compact_ofNat_junk _ _ _ _
      (by have := hsum al (f (StaggerBoolean.leftGroup mode) (BitVec.allOnes 32) bl cl dl) wl kl
          simp only [Nat.reducePow] at *; omega)
      (by have := hsum ar (f (StaggerBoolean.rightGroup mode) (BitVec.allOnes 32) br cr dr) wr kr
          simp only [Nat.reducePow] at *; omega)]
    exact h.1
  · rw [normalize_ofNat_junk _ _ _ _
      (by have := hsum al (f (StaggerBoolean.leftGroup mode) (BitVec.allOnes 32) bl cl dl) wl kl
          simp only [Nat.reducePow] at *; omega)
      (by have := hsum ar (f (StaggerBoolean.rightGroup mode) (BitVec.allOnes 32) br cr dr) wr kr
          simp only [Nat.reducePow] at *; omega)]
    exact h.2

#print axioms rawSum_canonical
#print axioms rawSum_pack
#print axioms rawSum_inputs
#print axioms normalize_ofNat_junk
#print axioms compact_ofNat_junk
#print axioms rawSum_inputs_junk
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRound
