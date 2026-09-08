import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFSlotBound

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Discharging the packed step's carried hypotheses

`PackedStepCorrected.correctedStep_represents` carries four hypotheses.  This
addendum removes two of them outright and reduces the other two to a single
`UInt32`-level fact.  It touches no frozen file.

* `hfit` / `hcarry` — DISCHARGED.  `packedRot` is `Clean`, and `clean_add_bounds`
  derives both side conditions from `Clean` alone.  That is the reasoning
  already inside `inv_of_rot_add`, exposed here rather than restated.
* `hsum0` / `hsum1` — reduced to lane-level `Nat` sums via `roundSum_lane0` /
  `roundSum_lane1`, using Pascal's `packedFWord_slot0_lt33` for the only
  non-trivial bound.  What remains is `UInt32` arithmetic and nothing else.

## The fact that makes the sum projections unconditional

`lane0N` and `lane1N` are **invariant under the `UInt256` wrap**.  For lane 0
that is immediate (`2 ^ 32 ∣ 2 ^ 256`).  For lane 1 it is not obvious and is
proved below: writing `s = 2 ^ 256 * q + w`, the quotient picks up
`2 ^ 192 * q`, and `2 ^ 32 ∣ 2 ^ 192`, so it vanishes under the `% 2 ^ 32`.

This matters because root's `SpreadReads` deliberately leaves the loaded word's
`high <<< 128` component UNBOUNDED, so `packedFWord + X` genuinely can exceed
`2 ^ 256`.  An earlier draft of mine carried a `fits : X < 2 ^ 224` field to
rule that out; it was not derivable from `loadPair_spec` and, as it turns out,
was never needed — the wrap is harmless to both lanes.

STATUS: WRITTEN, NOT ELABORATED.  Zero `sorry`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepBounds

open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected

/-! ## 1.  `packedRot` is `Clean` -/

private theorem rotL_toNat (S : UInt256) (s : Nat) (hs : s < 32) :
    (UInt256.land
      (UInt256.shiftRight (UInt256.mul cMul (S &&& maskLR))
        (UInt256.ofNat (32 - s))) maskL).toNat
      = ((cN * (lane0N S.toNat + lane1N S.toNat * 2 ^ 64)) >>> (32 - s))
          &&& maskLN := by
  rw [word_toNat_land, maskL_toNat,
    Challenge.EvmProof.Word.shiftRight_toNat _ (show 32 - s < 256 by omega),
    mul_cMul_toNat]

private theorem rotR_toNat (S : UInt256) (s : Nat) (hs : s < 32) :
    (UInt256.land
      (UInt256.shiftRight (UInt256.mul cMul (S &&& maskLR))
        (UInt256.ofNat (32 - s))) maskR).toNat
      = ((cN * (lane0N S.toNat + lane1N S.toNat * 2 ^ 64)) >>> (32 - s))
          &&& maskRN := by
  rw [word_toNat_land, maskR_toNat,
    Challenge.EvmProof.Word.shiftRight_toNat _ (show 32 - s < 256 by omega),
    mul_cMul_toNat]

private theorem or_masked_self (a b : Nat) :
    ((a &&& maskLN) ||| (b &&& maskRN)) &&& maskLRN
      = (a &&& maskLN) ||| (b &&& maskRN) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, testBit_maskLN, testBit_maskRN,
    testBit_maskLRN]
  by_cases hi : i < 32
  · have h64 : ¬64 ≤ i := by omega
    simp [hi, h64]
  · by_cases h64 : 64 ≤ i
    · by_cases hw : i - 64 < 32 <;> simp [hi, h64, hw]
    · simp [hi, h64]

private theorem packedRot_toNat (S : UInt256) (sl sr : Nat)
    (hsl : sl < 32) (hsr : sr < 32) :
    (packedRot S sl sr).toNat
      = (((cN * (lane0N S.toNat + lane1N S.toNat * 2 ^ 64)) >>> (32 - sl))
            &&& maskLN)
        ||| (((cN * (lane0N S.toNat + lane1N S.toNat * 2 ^ 64)) >>> (32 - sr))
            &&& maskRN) := by
  rw [packedRot, word_toNat_lor, rotL_toNat S sl hsl, rotR_toNat S sr hsr]

/-- The rotate output is `Clean`: 32 bits per lane, no carry bit.  This is what
lets the round's trailing truncation mask be dropped. -/
theorem packedRot_clean (S : UInt256) (sl sr : Nat)
    (hsl : sl < 32) (hsr : sr < 32) : Clean (packedRot S sl sr) := by
  have hself : packedRot S sl sr = packedRot S sl sr &&& maskLR := by
    apply word_ext
    change (packedRot S sl sr).toNat =
      (UInt256.land (packedRot S sl sr) maskLR).toNat
    rw [word_toNat_land, maskLR_toNat, packedRot_toNat S sl sr hsl hsr,
      or_masked_self]
  rw [hself]
  exact masked_input_clean _

/-- Both side conditions of `represents_add`, from `Clean` alone. -/
theorem clean_add_bounds (R E : UInt256) (hR : Clean R) (hE : Clean E) :
    R.toNat + E.toNat < 2 ^ 256 ∧
      R.toNat % 2 ^ 64 + E.toNat % 2 ^ 64 < 2 ^ 64 := by
  have hnc : R.toNat % 2 ^ 64 + E.toNat % 2 ^ 64 < 2 ^ 64 := by
    calc R.toNat % 2 ^ 64 + E.toNat % 2 ^ 64 < 2 ^ 32 + 2 ^ 32 :=
          Nat.add_lt_add hR.low hE.low
      _ = 2 ^ 33 := by norm_num
      _ < 2 ^ 64 := by norm_num
  have hRb : R.toNat < 2 ^ 32 * 2 ^ 64 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)).mp hR.high
  have hEb : E.toNat < 2 ^ 32 * 2 ^ 64 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)).mp hE.high
  refine ⟨?_, hnc⟩
  calc R.toNat + E.toNat < 2 ^ 32 * 2 ^ 64 + 2 ^ 32 * 2 ^ 64 :=
        Nat.add_lt_add hRb hEb
    _ < 2 ^ 256 := by norm_num [← Nat.pow_add]

/-- **The step-boundary invariant is inductive.**  The asymmetry is forced:
`b' = rot + e` carries a carry bit, so `b`/`c` can only ever be `Inv`. -/
theorem correctedStep_regsOk (r sl sr : Nat) (g : Regs) (X K : UInt256)
    (hsl : sl < 32) (hsr : sr < 32) (h : RegsOk g) :
    RegsOk (correctedStep r sl sr g X K) := by
  constructor
  · exact h.he
  · exact inv_of_rot_add _ _
      (packedRot_clean (roundSum r g X K) sl sr hsl hsr) h.he
  · exact h.hb
  · exact packedRol10_clean g.c
  · exact h.hd

/-! ## 2.  Lane projections are invariant under the `UInt256` wrap -/

theorem lane0N_mod_pow256 (s : Nat) : lane0N (s % 2 ^ 256) = lane0N s := by
  simp only [lane0N_eq_mod]
  exact Nat.mod_mod_of_dvd s (by norm_num : (2 : Nat) ^ 32 ∣ 2 ^ 256)

theorem lane1N_mod_pow256 (s : Nat) : lane1N (s % 2 ^ 256) = lane1N s := by
  have hpos : 0 < (2 : Nat) ^ 64 := Nat.two_pow_pos 64
  have hp : (2 : Nat) ^ 192 * 2 ^ 64 = 2 ^ 256 := by norm_num [← Nat.pow_add]
  have hs : s = s % 2 ^ 256 + 2 ^ 192 * (s / 2 ^ 256) * 2 ^ 64 := by
    have h := Nat.div_add_mod s (2 ^ 256)
    calc s = 2 ^ 256 * (s / 2 ^ 256) + s % 2 ^ 256 := h.symm
      _ = s % 2 ^ 256 + 2 ^ 192 * (s / 2 ^ 256) * 2 ^ 64 := by
          rw [← hp]; ring
  have hz : 2 ^ 192 * (s / 2 ^ 256) % 2 ^ 32 = 0 := by
    have hq : (2 : Nat) ^ 32 * 2 ^ 160 = 2 ^ 192 := by norm_num [← Nat.pow_add]
    have hr : (2 : Nat) ^ 192 * (s / 2 ^ 256)
        = 2 ^ 32 * (2 ^ 160 * (s / 2 ^ 256)) := by
      rw [← Nat.mul_assoc, hq]
    rw [hr]
    exact Nat.mul_mod_right _ _
  simp only [lane1N_eq_div]
  conv_rhs => rw [hs]
  rw [Nat.add_mul_div_right _ _ hpos, Nat.add_mod, hz, Nat.add_zero]
  simp

theorem lane0N_word_add (a b : UInt256) :
    lane0N (a + b).toNat = (lane0N a.toNat + lane0N b.toNat) % 2 ^ 32 := by
  rw [word_toNat_add, lane0N_mod_pow256, lane0N_add]

theorem lane1N_word_add (a b : UInt256)
    (h : a.toNat % 2 ^ 64 + b.toNat % 2 ^ 64 < 2 ^ 64) :
    lane1N (a + b).toNat = (lane1N a.toNat + lane1N b.toNat) % 2 ^ 32 := by
  rw [word_toNat_add, lane1N_mod_pow256, lane1N_add _ _ h]

theorem slot0_word_add (a b : UInt256)
    (h : a.toNat % 2 ^ 64 + b.toNat % 2 ^ 64 < 2 ^ 64) :
    (a + b).toNat % 2 ^ 64 = a.toNat % 2 ^ 64 + b.toNat % 2 ^ 64 := by
  rw [word_toNat_add,
    Nat.mod_mod_of_dvd _ (by norm_num : (2 : Nat) ^ 64 ∣ 2 ^ 256)]
  exact (slot_add a.toNat b.toNat h).1

/-! ## 3.  The round sum, lane by lane -/

section RoundSum

variable (r : Nat) (g : Regs) (X K : UInt256)

/-- The slot-0 no-carry chain for the round's three additions, from Pascal's
`packedFWord_slot0_lt33` plus `Clean` on `a` and `K` and `WordOk` on `X`.
Every one of these is falsifiable: any operand whose slot 0 reaches `2 ^ 63`
breaks the corresponding conjunct. -/
theorem roundSum_no_carry (hr : r < 5) (hregs : RegsOk g)
    (hX : X.toNat % 2 ^ 64 < 2 ^ 32) (hK : K.toNat % 2 ^ 64 < 2 ^ 32) :
    (PackedFBridge.packedFWord r g.b g.c g.d).toNat % 2 ^ 64 + X.toNat % 2 ^ 64 < 2 ^ 64 ∧
      ((PackedFBridge.packedFWord r g.b g.c g.d) + X).toNat % 2 ^ 64 + g.a.toNat % 2 ^ 64 < 2 ^ 64 ∧
      ((PackedFBridge.packedFWord r g.b g.c g.d) + X + g.a).toNat % 2 ^ 64 + K.toNat % 2 ^ 64 < 2 ^ 64 := by
  have hf :
      (PackedFBridge.packedFWord r g.b g.c g.d).toNat % 2 ^ 64 < 2 ^ 33 :=
    Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFSlotBound.packedFWord_slot0_lt33
      r g.b g.c g.d hr hregs.hb hregs.hc hregs.hd
  have ha : g.a.toNat % 2 ^ 64 < 2 ^ 32 := hregs.ha.low
  have h1 : (PackedFBridge.packedFWord r g.b g.c g.d).toNat % 2 ^ 64 + X.toNat % 2 ^ 64 < 2 ^ 64 := by
    have : (2 : Nat) ^ 33 + 2 ^ 32 < 2 ^ 64 := by norm_num
    omega
  have e1 := slot0_word_add (PackedFBridge.packedFWord r g.b g.c g.d) X h1
  have h2 : ((PackedFBridge.packedFWord r g.b g.c g.d) + X).toNat % 2 ^ 64 + g.a.toNat % 2 ^ 64 < 2 ^ 64 := by
    have : (2 : Nat) ^ 33 + 2 ^ 32 + 2 ^ 32 < 2 ^ 64 := by norm_num
    omega
  have e2 := slot0_word_add ((PackedFBridge.packedFWord r g.b g.c g.d) + X) g.a h2
  have h3 : ((PackedFBridge.packedFWord r g.b g.c g.d) + X + g.a).toNat % 2 ^ 64 + K.toNat % 2 ^ 64 < 2 ^ 64 := by
    have : (2 : Nat) ^ 33 + 2 ^ 32 + 2 ^ 32 + 2 ^ 32 < 2 ^ 64 := by norm_num
    omega
  exact ⟨h1, h2, h3⟩

/-- Lane 0 of the round sum.  Needs NO carry hypothesis at all: `% 2 ^ 32` is
compatible with `+`, and the wrap is invisible to lane 0. -/
theorem roundSum_lane0 :
    lane0N (roundSum r g X K).toNat
      = (lane0N (PackedFBridge.packedFWord r g.b g.c g.d).toNat + lane0N X.toNat + lane0N g.a.toNat
          + lane0N K.toNat) % 2 ^ 32 := by
  show lane0N ((PackedFBridge.packedFWord r g.b g.c g.d) + X + g.a + K).toNat = _
  rw [lane0N_word_add, lane0N_word_add, lane0N_word_add]
  omega

/-- Lane 1 of the round sum, under exactly the slot-0 no-carry chain. -/
theorem roundSum_lane1 (hr : r < 5) (hregs : RegsOk g)
    (hX : X.toNat % 2 ^ 64 < 2 ^ 32) (hK : K.toNat % 2 ^ 64 < 2 ^ 32) :
    lane1N (roundSum r g X K).toNat
      = (lane1N (PackedFBridge.packedFWord r g.b g.c g.d).toNat + lane1N X.toNat + lane1N g.a.toNat
          + lane1N K.toNat) % 2 ^ 32 := by
  obtain ⟨h1, h2, h3⟩ := roundSum_no_carry r g X K hr hregs hX hK
  show lane1N ((PackedFBridge.packedFWord r g.b g.c g.d) + X + g.a + K).toNat = _
  rw [lane1N_word_add _ _ h3, lane1N_word_add _ _ h2, lane1N_word_add _ _ h1]
  omega

end RoundSum

/-! ## 4.  The round, with `hfit` / `hcarry` gone -/

/-- `correctedStep_represents` with the two `ADD` side conditions discharged
from `RegsOk`.  `hsum0` / `hsum1` remain, and MUST be discharged by the composed
final theorem — they are not to be accepted into a `BlockKernel`. -/
theorem correctedStep_represents_of_regs
    (r sl sr : Nat) (g : Regs) (X K : UInt256)
    (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 x0 x1 k0 k1 : UInt32)
    (hr : r < 5) (hsl0 : 0 < sl) (hsl : sl < 32)
    (hsr0 : 0 < sr) (hsr : sr < 32)
    (hentry : stepEntry g a0 a1 b0 b1 c0 c1 d0 d1 e0 e1)
    (hregs : RegsOk g)
    (hsum0 : UInt32.ofNat (lane0N (roundSum r g X K).toNat)
        = a0 + Crypto.Ripemd160.f r b0 c0 d0 + x0 + k0)
    (hsum1 : UInt32.ofNat (lane1N (roundSum r g X K).toNat)
        = a1 + Crypto.Ripemd160.f (4 - r) b1 c1 d1 + x1 + k1) :
    Represents (correctedStep r sl sr g X K).a e0 e1 ∧
      Represents (correctedStep r sl sr g X K).b
        (Crypto.Ripemd160.rotl32 (a0 + Crypto.Ripemd160.f r b0 c0 d0 + x0 + k0)
          sl + e0)
        (Crypto.Ripemd160.rotl32
          (a1 + Crypto.Ripemd160.f (4 - r) b1 c1 d1 + x1 + k1) sr + e1) ∧
      Represents (correctedStep r sl sr g X K).c b0 b1 ∧
      Represents (correctedStep r sl sr g X K).d
        (Crypto.Ripemd160.rotl32 c0 10) (Crypto.Ripemd160.rotl32 c1 10) ∧
      Represents (correctedStep r sl sr g X K).e d0 d1 := by
  have hbnd := clean_add_bounds _ _
    (packedRot_clean (roundSum r g X K) sl sr hsl hsr) hregs.he
  exact correctedStep_represents r sl sr g X K a0 a1 b0 b1 c0 c1 d0 d1 e0 e1
    x0 x1 k0 k1 hr hsl0 hsl hsr0 hsr hentry hsum0 hsum1 hbnd.1 hbnd.2

/-! ## 5.  The `UInt32` bridge, and the unconditional round

The last residual.  `roundSum_lane0` / `roundSum_lane1` land on a four-term
`Nat` sum taken mod `2 ^ 32`, in the generator's order `(f, X, a, K)`; the
specification's round is a four-term `UInt32` sum in the order `(a, f, X, K)`.
`UInt32` addition IS `Nat` addition mod `2 ^ 32`, so the two agree — but the
reassociation and the commutation have to be done explicitly. -/

private theorem ofNat_add_mod (p q : Nat) :
    UInt32.ofNat ((p + q) % 2 ^ 32)
      = UInt32.ofNat p + UInt32.ofNat q := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add, UInt32.toNat_ofNat']
  omega

/-- The bridge: a four-term `Nat` sum mod `2 ^ 32`, reassociated and commuted
into the specification's `UInt32` order.  No bounds are needed — `UInt32.ofNat`
already reduces mod `2 ^ 32`. -/
theorem ofNat_roundSum (F Xl A Kl : Nat) :
    UInt32.ofNat ((F + Xl + A + Kl) % 2 ^ 32)
      = UInt32.ofNat A + UInt32.ofNat F + UInt32.ofNat Xl + UInt32.ofNat Kl := by
  have h : (F + Xl + A + Kl) % 2 ^ 32
      = (((A + F) % 2 ^ 32 + Xl) % 2 ^ 32 + Kl) % 2 ^ 32 := by omega
  rw [h, ofNat_add_mod, ofNat_add_mod, ofNat_add_mod]

/-- `hsum0`, DISCHARGED. -/
theorem hsum0_of (r : Nat) (g : Regs) (X K : UInt256)
    (a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 k0 k1 : UInt32) (hr : r < 5)
    (ha : Represents g.a a0 a1) (hb : Represents g.b b0 b1)
    (hc : Represents g.c c0 c1) (hd : Represents g.d d0 d1)
    (hX : WordOk X x0 x1) (hK : ConstOk K k0 k1) :
    UInt32.ofNat (lane0N (roundSum r g X K).toNat)
      = a0 + Crypto.Ripemd160.f r b0 c0 d0 + x0 + k0 := by
  rw [roundSum_lane0 r g X K, ofNat_roundSum,
    PackedFBridge.packedFWord_lane0_project r g.b g.c g.d hr,
    hb.1, hc.1, hd.1, ha.1, hX.lane0, hK.lane0]

/-- `hsum1`, DISCHARGED.  Needs the slot-0 no-carry chain, hence `hregs`. -/
theorem hsum1_of (r : Nat) (g : Regs) (X K : UInt256)
    (a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 k0 k1 : UInt32) (hr : r < 5)
    (hregs : RegsOk g)
    (ha : Represents g.a a0 a1) (hb : Represents g.b b0 b1)
    (hc : Represents g.c c0 c1) (hd : Represents g.d d0 d1)
    (hX : WordOk X x0 x1) (hK : ConstOk K k0 k1) :
    UInt32.ofNat (lane1N (roundSum r g X K).toNat)
      = a1 + Crypto.Ripemd160.f (4 - r) b1 c1 d1 + x1 + k1 := by
  rw [roundSum_lane1 r g X K hr hregs hX.slot0 hK.clean.low, ofNat_roundSum,
    PackedFBridge.packedFWord_lane1_project r g.b g.c g.d hr,
    hb.2, hc.2, hd.2, ha.2, hX.lane1, hK.lane1]

/-- **The one-round correspondence, UNCONDITIONAL.**  Every hypothesis that
`correctedStep_represents` carried is now discharged: `hfit` / `hcarry` from
`Clean`, `hsum0` / `hsum1` from Pascal's slot bound and the lane projections.
What remains are only facts about the operands themselves — the entry
relation, the step-boundary bounds, and the load/constant relations. -/
theorem correctedStep_represents_final
    (r sl sr : Nat) (g : Regs) (X K : UInt256)
    (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 x0 x1 k0 k1 : UInt32)
    (hr : r < 5) (hsl0 : 0 < sl) (hsl : sl < 32)
    (hsr0 : 0 < sr) (hsr : sr < 32)
    (hentry : stepEntry g a0 a1 b0 b1 c0 c1 d0 d1 e0 e1)
    (hregs : RegsOk g) (hX : WordOk X x0 x1) (hK : ConstOk K k0 k1) :
    Represents (correctedStep r sl sr g X K).a e0 e1 ∧
      Represents (correctedStep r sl sr g X K).b
        (Crypto.Ripemd160.rotl32 (a0 + Crypto.Ripemd160.f r b0 c0 d0 + x0 + k0)
          sl + e0)
        (Crypto.Ripemd160.rotl32
          (a1 + Crypto.Ripemd160.f (4 - r) b1 c1 d1 + x1 + k1) sr + e1) ∧
      Represents (correctedStep r sl sr g X K).c b0 b1 ∧
      Represents (correctedStep r sl sr g X K).d
        (Crypto.Ripemd160.rotl32 c0 10) (Crypto.Ripemd160.rotl32 c1 10) ∧
      Represents (correctedStep r sl sr g X K).e d0 d1 := by
  obtain ⟨ha, hb, hc, hd, he⟩ := hentry
  exact correctedStep_represents_of_regs r sl sr g X K a0 a1 b0 b1 c0 c1
    d0 d1 e0 e1 x0 x1 k0 k1 hr hsl0 hsl hsr0 hsr ⟨ha, hb, hc, hd, he⟩ hregs
    (hsum0_of r g X K a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 k0 k1 hr ha hb hc hd hX hK)
    (hsum1_of r g X K a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 k0 k1 hr hregs
      ha hb hc hd hX hK)

#print axioms ofNat_roundSum
#print axioms hsum0_of
#print axioms hsum1_of
#print axioms correctedStep_represents_final
#print axioms packedRot_clean
#print axioms clean_add_bounds
#print axioms correctedStep_regsOk
#print axioms lane1N_mod_pow256
#print axioms roundSum_lane0
#print axioms roundSum_lane1
#print axioms correctedStep_represents_of_regs

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepBounds
