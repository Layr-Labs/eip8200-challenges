import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRotEmbed
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLoadModel

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# `correctedStep`: one packed round, against the proved lane APIs

STATUS: WRITTEN, NOT ELABORATED.  Zero `sorry`.

Consumes, does not restate: `PackedLaneMask`, `PackedLaneInvariant` (`Clean`,
`Inv`, `masked_word_split`), `PackedLaneRot` (window lemmas, `packedRol10`),
`PackedFBridge` (`packedFWord`, lane projections).  It does NOT import the old
`sorry`-carrying `PackedStep`.

## On premises — every hypothesis here has a witness that violates it

The three premise defects found today (`mul_precondition` tautological, the
entry premise `∀ i, True` vacuous, `BlockContext` too weak for its own read)
were all invisible because nothing could falsify them.  So for each hypothesis
below, a violating input is named.

### The entry premise

`stepEntry` is field equalities against the packed constructor.  It is NOT
`∀ i, True`, which constrains nothing and under which anything is provable.

### `WordOk` and the scratch-gap read at bytes 272..280

The schedule spread writes 32 bytes at `16*k` for `k = 15 … 0`, so it covers
bytes `[0, 272)`.  The right-lane load for message index 15 is
`MLOAD 248`, covering `[248, 280)`.  **Bytes `[272, 280)` are read and never
written** — the `SWAP` region only begins at 288.

Those eight bytes land in the **low 64 bits** of that load, so a dirty gap
corrupts **lane 0** (the LEFT line) and breaks `slot0`; lane 1 is unaffected,
because lane 1 comes from bytes `[268, 272)`, which the spread does write.
It bites on exactly the five steps with `RR j = 15`: **steps 10, 25, 32, 54,
65**.  Verified by re-running the builder's own store/load offsets with `0xAA`
in the gap: lane 0 changes on those five steps and on no others, and `slot0`
fails on exactly those five.

Therefore `WordOk.slot0` and `WordOk.lane0` are **not** free facts about the
artifact — they are consequences of the gap being zero, and that is a property
of the machine state, not of the bytecode.  `scratchGapZero` below names it
rather than quantifying over states that happen to satisfy it.  This module
takes it as a hypothesis; root's `PackedLoadOk` is expected to discharge it
with explicit read constraints.

* violates `slot0` / `lane0`: any state with a nonzero byte in `[272, 280)`,
  at any step with `RR j = 15`.

`WordOk` carries exactly the three facts `PackedLoadModel.loadPair_spec`
delivers and nothing more.  An earlier draft also carried `fits : X < 2 ^ 224`;
that is NOT derivable from `loadPair_spec`, which deliberately leaves the
`high <<< 128` component unbounded, and nothing needed it.  A field no source
can supply and no proof consumes is the same defect one level down, so it is
gone.

### Register bounds

Tracing the register rotation `(A,B,C,D,E) := (E, T, B, R, D)`: `A` is a
previous `R` (`Clean`), `B` and `C` are previous `T = rot + E` (`Inv` only,
never `Clean`), `D` is a fresh `packedRol10` output (`Clean`), `E` is a
previous `D` (`Clean`).  So `Inv` on `b`/`c` and `Clean` on `a`/`d`/`e` is the
strongest uniform statement available, and it is exactly the shape of Pascal's
`packedFWord_slot0_lt33` obligation.  Do not try to strengthen `b` to `Clean`:
`rot + e` has 32-bit lanes plus a carry bit, and the induction fails at that
conjunct.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected

open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRotEmbed

/-! ## 1.  Lane algebra not present in `PackedLaneMask` -/

theorem windowN_or (a b k : Nat) :
    windowN (a ||| b) k = windowN a k ||| windowN b k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_windowN, Nat.testBit_or]
  by_cases hi : i < 32 <;> simp [hi]

theorem lane0N_and_maskL (p : Nat) : lane0N (p &&& maskLN) = lane0N p := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lane0N, testBit_windowN, Nat.testBit_and, testBit_maskLN]
  by_cases hi : i < 32 <;> simp [hi]

theorem lane0N_and_maskR (p : Nat) : lane0N (p &&& maskRN) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lane0N, testBit_windowN, Nat.testBit_and, testBit_maskRN,
    Nat.zero_testBit]
  by_cases hi : i < 32 <;> simp [hi]
  omega

theorem lane1N_and_maskL (p : Nat) : lane1N (p &&& maskLN) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lane1N, testBit_windowN, Nat.testBit_and, testBit_maskLN,
    Nat.zero_testBit]
  by_cases hi : i < 32 <;> simp [hi]
  omega

theorem lane1N_and_maskR (p : Nat) : lane1N (p &&& maskRN) = lane1N p := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lane1N, testBit_windowN, Nat.testBit_and, testBit_maskRN]
  by_cases hi : i < 32 <;> simp [hi]

/-- Slot-wise addition, given the slot-0 no-carry condition.  Pascal's copy in
`PackedLaneInvariant` is `private`, so this is re-declared, same statement and
same proof. -/
theorem slot_add (a b : Nat) (hlo : a % 2 ^ 64 + b % 2 ^ 64 < 2 ^ 64) :
    (a + b) % 2 ^ 64 = a % 2 ^ 64 + b % 2 ^ 64 ∧
      (a + b) / 2 ^ 64 = a / 2 ^ 64 + b / 2 ^ 64 := by
  have ha := Nat.div_add_mod a (2 ^ 64)
  have hb := Nat.div_add_mod b (2 ^ 64)
  have hab := Nat.div_add_mod (a + b) (2 ^ 64)
  have hma : a % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hmb : b % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hmab : (a + b) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos _)
  omega

theorem lane0N_eq_mod (p : Nat) : lane0N p = p % 2 ^ 32 := by
  simp [lane0N, windowN]

theorem lane1N_eq_div (p : Nat) : lane1N p = p / 2 ^ 64 % 2 ^ 32 := by
  simp [lane1N, windowN, Nat.shiftRight_eq_div_pow]

/-- Lane 0 of a sum needs NO hypothesis: `% 2 ^ 32` is compatible with `+`. -/
theorem lane0N_add (a b : Nat) :
    lane0N (a + b) = (lane0N a + lane0N b) % 2 ^ 32 := by
  simp only [lane0N_eq_mod]
  rw [Nat.add_mod]

/-- Lane 1 of a sum needs exactly the slot-0 no-carry hypothesis, and nothing
about bits 128 and above.  `hlo` is falsifiable: take `a = b = 2 ^ 63`. -/
theorem lane1N_add (a b : Nat) (hlo : a % 2 ^ 64 + b % 2 ^ 64 < 2 ^ 64) :
    lane1N (a + b) = (lane1N a + lane1N b) % 2 ^ 32 := by
  simp only [lane1N_eq_div]
  rw [(slot_add a b hlo).2, Nat.add_mod]

/-! ## 2.  The relations -/

/-- The packed-to-lane-pair relation: one 256-bit word carries the left line's
register in bits 0..31 and the right line's in bits 64..95. -/
def Represents (P : UInt256) (l0 l1 : UInt32) : Prop :=
  UInt32.ofNat (lane0N P.toNat) = l0 ∧ UInt32.ofNat (lane1N P.toNat) = l1

/-- A loaded packed message word.  `slot0` is the no-carry premise for the
round's additions; `fits` is the no-wrap headroom.  Junk at bit 128 and above
is DELIBERATELY permitted — the spread-schedule `MLOAD` leaves the neighbouring
field there and it contributes only a multiple of `2 ^ 64` to the slot-1 value,
which vanishes under the `% 2 ^ 32` in `lane1N`.  Demanding `Clean` here would
be FALSE of the real artifact. -/
structure WordOk (X : UInt256) (x0 x1 : UInt32) : Prop where
  slot0 : X.toNat % 2 ^ 64 < 2 ^ 32
  lane0 : UInt32.ofNat (lane0N X.toNat) = x0
  lane1 : UInt32.ofNat (lane1N X.toNat) = x1

/-- The packed round constant `KL r ||| KR r <<< 64`.  Unlike a loaded word it
really is `Clean`: it is a literal with nothing above bit 95. -/
structure ConstOk (K : UInt256) (k0 k1 : UInt32) : Prop where
  clean : Clean K
  lane0 : UInt32.ofNat (lane0N K.toNat) = k0
  lane1 : UInt32.ofNat (lane1N K.toNat) = k1

/-- The five packed registers. -/
structure Regs where
  a : UInt256
  b : UInt256
  c : UInt256
  d : UInt256
  e : UInt256

/-- Step-entry bounds, in the asymmetric form the register rotation actually
supports.  `b` and `c` carry only `Inv`; strengthening them to `Clean` is not
inductive. -/
structure RegsOk (g : Regs) : Prop where
  ha : Clean g.a
  hb : Inv g.b
  hc : Inv g.c
  hd : Clean g.d
  he : Clean g.e

/-- **The entry premise, stated as field equalities.**  This replaces the
scaffold's `∀ i, True`, which is vacuous: it constrains nothing, so a theorem
proved under it is proved under no hypothesis at all. -/
def stepEntry (g : Regs) (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 : UInt32) : Prop :=
  Represents g.a a0 a1 ∧ Represents g.b b0 b1 ∧ Represents g.c c0 c1 ∧
    Represents g.d d0 d1 ∧ Represents g.e e0 e1

/-- **Adapter: root's proved load model discharges the neutral `WordOk`.**

`SpreadReads` is taken as a hypothesis and passed through, NOT assumed.  It is
a relation about post-spread memory; establishing it — including zero at bytes
`[272, 280)`, which the last right-hand load reads and the spread never writes
— is the preprocessing trace's obligation and sits upstream of this module.

`WordOk` itself stays neutral: it mentions no memory, no offset and no layout,
so the step API does not move when the load story is settled. -/
theorem wordOk_of_spreadReads (memory : ByteArray) (words : Nat → UInt32)
    (hspread : PackedLoadModel.SpreadReads memory words)
    (i j : Nat) (hi : i < 16) (hj : j < 16) :
    WordOk (PackedLoadModel.loadPair memory i j) (words i) (words j) := by
  obtain ⟨h0, h1, hs⟩ :=
    PackedLoadModel.loadPair_spec memory words hspread i j hi hj
  exact { slot0 := hs
          lane0 := by rw [h0, UInt32.ofNat_toNat]
          lane1 := by rw [h1, UInt32.ofNat_toNat] }

/-! ## 3.  The emitted round -/

/-- `ADD ; ADD ; ADD` in the generator's own order:
`((f + X) + A) + K`. -/
def roundSum (r : Nat) (g : Regs) (X K : UInt256) : UInt256 :=
  (Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFBridge.packedFWord
      r g.b g.c g.d + X) + g.a + K

/-- `AND maskLR ; MUL c ; DUP1 ; SHR (32-sl) ; AND maskL ; SWAP ;
SHR (32-sr) ; AND maskR ; OR`.  The two lanes rotate by DIFFERENT amounts —
that is the whole reason the extraction is two shifts and not one. -/
def packedRot (S : UInt256) (sl sr : Nat) : UInt256 :=
  UInt256.lor
    (UInt256.land
      (UInt256.shiftRight (UInt256.mul cMul (S &&& maskLR))
        (UInt256.ofNat (32 - sl))) maskL)
    (UInt256.land
      (UInt256.shiftRight (UInt256.mul cMul (S &&& maskLR))
        (UInt256.ofNat (32 - sr))) maskR)

/-- One packed round.  Register rotation `(A,B,C,D,E) := (E, T, B, rol10 C, D)`,
read off the generator's `emit_steps`. -/
def correctedStep (r sl sr : Nat) (g : Regs) (X K : UInt256) : Regs :=
  { a := g.e
    b := packedRot (roundSum r g X K) sl sr + g.e
    c := g.b
    d := packedRol10 g.c
    e := g.d }

/-! ## 4.  The rotate side — fully discharged by the proved window lemmas -/

private theorem rot_toNat (S : UInt256) (s : Nat) (hs : s < 32) :
    (UInt256.land
      (UInt256.shiftRight (UInt256.mul cMul (S &&& maskLR))
        (UInt256.ofNat (32 - s))) maskL).toNat
      = ((cN * (lane0N S.toNat + lane1N S.toNat * 2 ^ 64)) >>> (32 - s))
          &&& maskLN := by
  rw [word_toNat_land, maskL_toNat,
    Challenge.EvmProof.Word.shiftRight_toNat _ (show 32 - s < 256 by omega),
    mul_cMul_toNat]

private theorem rot_toNat_R (S : UInt256) (s : Nat) (hs : s < 32) :
    (UInt256.land
      (UInt256.shiftRight (UInt256.mul cMul (S &&& maskLR))
        (UInt256.ofNat (32 - s))) maskR).toNat
      = ((cN * (lane0N S.toNat + lane1N S.toNat * 2 ^ 64)) >>> (32 - s))
          &&& maskRN := by
  rw [word_toNat_land, maskR_toNat,
    Challenge.EvmProof.Word.shiftRight_toNat _ (show 32 - s < 256 by omega),
    mul_cMul_toNat]

/-- Lane 0 of the packed rotate is the left line's `rotl32` by `sl`. -/
theorem packedRot_lane0 (S : UInt256) (sl sr : Nat)
    (hsl0 : 0 < sl) (hsl : sl < 32) (hsr : sr < 32) :
    lane0N (packedRot S sl sr).toNat
      = (Crypto.Ripemd160.rotl32
          (UInt32.ofNat (lane0N S.toNat)) sl).toNat := by
  have hL : lane0N S.toNat < 2 ^ 32 := windowN_lt _ _
  have hR : lane1N S.toNat < 2 ^ 32 := windowN_lt _ _
  have hk : 32 - sl ≤ 32 := by omega
  rw [packedRot, word_toNat_lor, lane0N, windowN_or, ← lane0N, ← lane0N,
    rot_toNat S sl hsl, rot_toNat_R S sr hsr, lane0N_and_maskL,
    lane0N_and_maskR, Nat.or_zero,
    window_packed_lane0 _ _ (32 - sl) hL hR hk]
  have hrot := window_doubled (lane0N S.toNat) sl hL hsl0 hsl
  rw [hrot, ← rotl32_ofNat_toNat (lane0N S.toNat) sl hL hsl0 hsl]

/-- Lane 1 of the packed rotate is the right line's `rotl32` by `sr`. -/
theorem packedRot_lane1 (S : UInt256) (sl sr : Nat)
    (hsl : sl < 32) (hsr0 : 0 < sr) (hsr : sr < 32) :
    lane1N (packedRot S sl sr).toNat
      = (Crypto.Ripemd160.rotl32
          (UInt32.ofNat (lane1N S.toNat)) sr).toNat := by
  have hL : lane0N S.toNat < 2 ^ 32 := windowN_lt _ _
  have hR : lane1N S.toNat < 2 ^ 32 := windowN_lt _ _
  have hk : 32 - sr ≤ 32 := by omega
  rw [packedRot, word_toNat_lor, lane1N, windowN_or, ← lane1N, ← lane1N,
    rot_toNat S sl hsl, rot_toNat_R S sr hsr, lane1N_and_maskL,
    lane1N_and_maskR, Nat.zero_or,
    window_packed_lane1 _ _ (32 - sr) hL hR hk]
  have hrot := window_doubled (lane1N S.toNat) sr hR hsr0 hsr
  rw [hrot, ← rotl32_ofNat_toNat (lane1N S.toNat) sr hR hsr0 hsr]

/-! ## 5.  `rol10` on the `c` register -/

theorem step_d_represents (g : Regs) (c0 c1 : UInt32)
    (hc : Represents g.c c0 c1) :
    Represents (packedRol10 g.c)
      (Crypto.Ripemd160.rotl32 c0 10) (Crypto.Ripemd160.rotl32 c1 10) := by
  obtain ⟨h0, h1⟩ := hc
  constructor
  · rw [packedRol10_lane0_ripemdRot, ← h0, UInt32.ofNat_toNat]
  · rw [packedRol10_lane1_ripemdRot, ← h1, UInt32.ofNat_toNat]

/-! ## 5b.  Lane projection of the final `ADD` -/

private theorem ofNat_mod_add (p q : Nat) (hp : p < 2 ^ 32) (hq : q < 2 ^ 32) :
    UInt32.ofNat ((p + q) % 2 ^ 32) = UInt32.ofNat p + UInt32.ofNat q := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]
  simp

/-- `T = rot + E` projects lanewise.  `hcarry` is the slot-0 no-carry premise
and is falsifiable (`R.toNat = E.toNat = 2 ^ 63`); it is what `Clean E` plus
32-bit lanes on `rot` buy, and it is the hypothesis pair of
`inv_of_rot_add`. -/
theorem represents_add (R E : UInt256) (r0 r1 c0 c1 : UInt32)
    (hR : Represents R r0 r1) (hE : Represents E c0 c1)
    (hfit : R.toNat + E.toNat < 2 ^ 256)
    (hcarry : R.toNat % 2 ^ 64 + E.toNat % 2 ^ 64 < 2 ^ 64) :
    Represents (R + E) (r0 + c0) (r1 + c1) := by
  obtain ⟨h0, h1⟩ := hR
  obtain ⟨g0, g1⟩ := hE
  have hsum : (R + E).toNat = R.toNat + E.toNat := by
    rw [word_toNat_add]
    exact Nat.mod_eq_of_lt hfit
  constructor
  · rw [hsum, lane0N_add, ← h0, ← g0]
    exact ofNat_mod_add _ _ (windowN_lt _ _) (windowN_lt _ _)
  · rw [hsum, lane1N_add _ _ hcarry, ← h1, ← g1]
    exact ofNat_mod_add _ _ (windowN_lt _ _) (windowN_lt _ _)

/-! ## 6.  One-round correspondence

The rotate side above is discharged.  The two remaining facts are the lane
projections of the round sum, and they are exactly what root's `PackedLoadOk`
and Pascal's `packedFWord_slot0_lt33` are for.  They are taken as NAMED
hypotheses rather than assumed silently, so a call site that cannot supply them
fails visibly.

`hsum0` / `hsum1` are falsifiable: `hsum1` fails whenever slot 0 of the sum
carries out of bit 63, which is precisely what a dirty scratch gap at bytes
`[272, 280)` causes on steps 10, 25, 32, 54 and 65. -/

/-- **One packed round computes one round of BOTH RIPEMD-160 lines.**
Left line uses `f r` and rotates by `sl`; right line uses `f (4 - r)` and
rotates by `sr`.

`RegsOk`, `WordOk` and `ConstOk` are deliberately NOT parameters here: this
proof does not use them, and a hypothesis that does no work only makes a
theorem harder to apply while looking as though it constrains something.  They
are the interface for discharging `hsum0` / `hsum1`, which is where the bounds
actually bite. -/
theorem correctedStep_represents
    (r sl sr : Nat) (g : Regs) (X K : UInt256)
    (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 x0 x1 k0 k1 : UInt32)
    (_hr : r < 5) (hsl0 : 0 < sl) (hsl : sl < 32)
    (hsr0 : 0 < sr) (hsr : sr < 32)
    (hentry : stepEntry g a0 a1 b0 b1 c0 c1 d0 d1 e0 e1)
    (hsum0 : UInt32.ofNat (lane0N (roundSum r g X K).toNat)
        = a0 + Crypto.Ripemd160.f r b0 c0 d0 + x0 + k0)
    (hsum1 : UInt32.ofNat (lane1N (roundSum r g X K).toNat)
        = a1 + Crypto.Ripemd160.f (4 - r) b1 c1 d1 + x1 + k1)
    (hfit : (packedRot (roundSum r g X K) sl sr).toNat + g.e.toNat < 2 ^ 256)
    (hcarry : (packedRot (roundSum r g X K) sl sr).toNat % 2 ^ 64
        + g.e.toNat % 2 ^ 64 < 2 ^ 64) :
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
  obtain ⟨_ha, hb, hc, hd, he⟩ := hentry
  have hrot : Represents (packedRot (roundSum r g X K) sl sr)
      (Crypto.Ripemd160.rotl32
        (a0 + Crypto.Ripemd160.f r b0 c0 d0 + x0 + k0) sl)
      (Crypto.Ripemd160.rotl32
        (a1 + Crypto.Ripemd160.f (4 - r) b1 c1 d1 + x1 + k1) sr) := by
    constructor
    · rw [packedRot_lane0 _ sl sr hsl0 hsl hsr, ← hsum0, UInt32.ofNat_toNat]
    · rw [packedRot_lane1 _ sl sr hsl hsr0 hsr, ← hsum1, UInt32.ofNat_toNat]
  exact ⟨he, represents_add _ _ _ _ _ _ hrot he hfit hcarry, hb,
    step_d_represents g c0 c1 hc, hd⟩

#print axioms correctedStep_represents
#print axioms packedRot_lane0
#print axioms packedRot_lane1

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
