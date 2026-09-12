import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRoundSemantic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Sums
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80CarryAdd
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80ScaledRotate

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80RoundSemantic

open Paired80Core Paired80Product Paired80Boolean Paired80Rotate Paired80Carry
open Paired80ScaledRotate

theorem low_blend (x y : BitVec 256) : low (blend x y) = low x := by
  have hm : upperMask.extractLsb' 0 32 = 0#32 :=
    low_pack 0#32 (BitVec.allOnes 32)
  simp only [blend, low, BitVec.extractLsb'_xor, BitVec.extractLsb'_and,
    hm, BitVec.and_zero, BitVec.xor_zero]

theorem high_blend (x y : BitVec 256) : high (blend x y) = high y := by
  have hm : upperMask.extractLsb' 80 32 = BitVec.allOnes 32 :=
    high_pack 0#32 (BitVec.allOnes 32)
  simp only [blend, high, BitVec.extractLsb'_xor, BitVec.extractLsb'_and,
    hm, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Equal rotation parameters use the single-shift form.  Otherwise the lane
needing the larger rotation is pre-scaled by `2^(difference)` before the shared
`factor` multiply, and one shift by `32 - min r s` rotates both lanes. -/
def rawRotate (x : BitVec 256) (r s : Nat) : BitVec 256 :=
  if r = s then (x * factor) >>> (32 - r)
  else if s < r then (scaleLow x (r - s) * factor) >>> (32 - s)
  else (scaleHigh x (s - r) * factor) >>> (32 - r)

theorem low_rawRotate (a b : BitVec 32) (r s : Nat)
    (hr0 : 0 < r) (hr : r < 17) (hs0 : 0 < s) (hs : s < 17) :
    low (rawRotate (pack a b) r s) = a.rotateLeft r := by
  by_cases h : r = s
  · simp only [rawRotate, h, ite_true]
    exact low_rotate_product a b s (h ▸ hr0) (by omega)
  · by_cases hlt : s < r
    · simp only [rawRotate, h, ite_false, hlt, ite_true]
      exact low_scaleLow a b r s hs0 hlt hr
    · simp only [rawRotate, h, ite_false, hlt]
      exact low_scaleHigh a b r s hr0 (by omega) hs

theorem high_rawRotate (a b : BitVec 32) (r s : Nat)
    (hr0 : 0 < r) (hr : r < 17) (hs0 : 0 < s) (hs : s < 17) :
    high (rawRotate (pack a b) r s) = b.rotateLeft s := by
  by_cases h : r = s
  · simp only [rawRotate, h, ite_true]
    exact high_rotate_product a b s hs0 (by omega)
  · by_cases hlt : s < r
    · simp only [rawRotate, h, ite_false, hlt, ite_true]
      exact high_scaleLow a b r s hs0 hs hlt hr
    · simp only [rawRotate, h, ite_false, hlt]
      exact high_scaleHigh a b r s hr0 (by omega) hs

theorem rawRotate_gap (a b : BitVec 32) (r s : Nat)
    (hr0 : 0 < r) (hr : r < 17) (hs0 : 0 < s) (hs : s < 17) :
    (rawRotate (pack a b) r s).getLsbD 48 = false := by
  by_cases h : r = s
  · simp only [rawRotate, h, ite_true]
    exact shifted_product_gap a b s (h ▸ hr0) (by omega)
  · by_cases hlt : s < r
    · simp only [rawRotate, h, ite_false, hlt, ite_true]
      exact gap_scaleLow a b r s hs0 hlt hr
    · simp only [rawRotate, h, ite_false, hlt]
      exact gap_scaleHigh a b r s hr0 (by omega) hs

def pairedSum (j : Nat) (a b c d word k : BitVec 256) : BitVec 256 :=
  (((a + pairedF j b c d) + word) + k) &&& pairMask

def scalarSum (j : Nat) (a b c d word k : BitVec 32) : BitVec 32 :=
  ((a + f j (BitVec.allOnes 32) b c d) + word) + k

theorem pairedSum_pack (j : Nat)
    (al ar bl br cl cr dl dr wl wr kl kr : BitVec 32) :
    pairedSum j (pack al ar) (pack bl br) (pack cl cr) (pack dl dr)
      (pack wl wr) (pack kl kr) =
      pack (scalarSum j al bl cl dl wl kl)
        (scalarSum (4 - j) ar br cr dr wr kr) := by
  unfold pairedSum scalarSum
  rw [pairedF_pack]
  exact and_four_adds al _ wl kl ar _ wr kr

def pairedT (j r s : Nat) (a b c d e word k : BitVec 256) : BitVec 256 :=
  (rawRotate (pairedSum j a b c d word k) r s + e) &&& pairMask

def scalarT (j r : Nat) (a b c d e word k : BitVec 32) : BitVec 32 :=
  (scalarSum j a b c d word k).rotateLeft r + e

theorem pairedT_pack (j r s : Nat)
    (hr0 : 0 < r) (hr : r < 17) (hs0 : 0 < s) (hs : s < 17)
    (al ar bl br cl cr dl dr el er wl wr kl kr : BitVec 32) :
    pairedT j r s (pack al ar) (pack bl br) (pack cl cr) (pack dl dr)
      (pack el er) (pack wl wr) (pack kl kr) =
      pack (scalarT j r al bl cl dl el wl kl)
        (scalarT (4 - j) s ar br cr dr er wr kr) := by
  unfold pairedT
  rw [pairedSum_pack, ← normalize_eq_and]
  rw [normalize_add_pack _ el er (rawRotate_gap _ _ r s hr0 hr hs0 hs)]
  rw [low_rawRotate _ _ r s hr0 hr hs0 hs, high_rawRotate _ _ r s hr0 hr hs0 hs]
  rfl

abbrev Lane (w : Nat) := PairedLaneRoundSemantic.Lane w

def packLane (l r : Lane 32) : Lane 256 :=
  ⟨pack l.a r.a, pack l.b r.b, pack l.c r.c, pack l.d r.d, pack l.e r.e⟩

def scalarStep (j r : Nat) (word k : BitVec 32) (q : Lane 32) : Lane 32 :=
  ⟨q.e, scalarT j r q.a q.b q.c q.d q.e word k, q.b, q.c.rotateLeft 10, q.d⟩

def pairedStep (j r s : Nat) (word k : BitVec 256) (q : Lane 256) : Lane 256 :=
  ⟨q.e, pairedT j r s q.a q.b q.c q.d q.e word k, q.b,
    normalize ((q.c * factor) >>> 22), q.d⟩

/-- All ten input state words, two message words and two constants are arbitrary. -/
theorem pairedStep_pack (j r s : Nat)
    (hr0 : 0 < r) (hr : r < 17) (hs0 : 0 < s) (hs : s < 17)
    (wl wr kl kr : BitVec 32) (l q : Lane 32) :
    pairedStep j r s (pack wl wr) (pack kl kr) (packLane l q) =
      packLane (scalarStep j r wl kl l) (scalarStep (4 - j) s wr kr q) := by
  cases l
  cases q
  unfold pairedStep packLane scalarStep
  rw [pairedT_pack j r s hr0 hr hs0 hs]
  rw [show 22 = 32 - 10 from rfl,
    normalize_rotate_product _ _ 10 (by decide) (by decide)]

#print axioms low_blend
#print axioms high_blend
#print axioms low_rawRotate
#print axioms high_rawRotate
#print axioms rawRotate_gap
#print axioms pairedSum_pack
#print axioms pairedT_pack
#print axioms pairedStep_pack

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80RoundSemantic
