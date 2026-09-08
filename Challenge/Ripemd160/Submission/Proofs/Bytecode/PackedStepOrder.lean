import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Emitted operand order vs definition order

The packed gate's round body computes the right value with the operands the
other way round from the way the arithmetic layer defines it, at six places.
These six lemmas convert **from the emitted order to the definition order** —
that direction, because the execution certificate produces the emitted form and
the proved arithmetic consumes the defined form.

They are stated over abstract operands, not over round 0's particular stack
slots, so they survive whichever way the generalisation decision goes: under a
round-0 bridge they apply directly, under a phase/group-indexed bridge they are
the base lemmas it instantiates.

## Associativity is NOT needed — all six are pure commutativity

I expected the round sum to need regrouping, because the emitted chain is
`ADD ADD DUP16 ADD`, three additions.  It does not.  Working the chain through:
the first `ADD` makes `f + X`, the second `(f + X) + a`, then `DUP16` lifts the
constant and the third makes `K + ((f + X) + a)`.  The definition is
`((f + X) + a) + K`.  The inner sub-term is *identical* on both sides, so the
difference is one `add_comm` at the top and no reassociation.

The `f` expression looked like the other assoc candidate and is not one either:
`mR ^^^ (b ^^^ c)` against `(b ^^^ c) ^^^ mR` differs by a single top-level
`xor_comm`, since the inner grouping already agrees.

So the bridge needs five `comm` rewrites for `f`, two for the rotate, two for
`rol10`, and one each for the load, the sum and the write-back.  No `assoc`
anywhere.  That makes the bridge cheaper than expected, and it is worth knowing
before someone budgets for a normalisation tactic.

## Three expression shapes, not five — and they explain the step lengths

Decoded the `f`-region of one round from each group, symbolically, from the raw:

    group 0  step  0  11 ops   (D ||| (mR &&& C)) ^^^ (mR ^^^ (C ^^^ B))
    group 1  step 16  17 ops   (mR &&& ((D ||| C) ^^^ (C &&& B))) ^^^ (D ^^^ (B &&& (D ^^^ C)))
    group 2  step 32   7 ops   D ^^^ (B ||| (mLR ^^^ C))
    group 3  step 48  17 ops   (mR &&& ((D ||| C) ^^^ (C &&& B))) ^^^ (C ^^^ (D &&& (C ^^^ B)))
    group 4  step 64  11 ops   (D ||| (mL &&& C)) ^^^ (mL ^^^ (C ^^^ B))

Group 4 is group 0 with the mask changed, so `f0_order` — stated over an
abstract mask — covers it with no new lemma.  Groups 1 and 3 share their whole
*correction* term and differ only in the base, and the base of group 3 is the
base of group 1 under `(p,q,r) := (D,B,C)`, so ONE parameterised select lemma
covers both.  That leaves two new lemmas, `fSelect_order` and `fShort_order`.

The region lengths 11/17/7/17/11 account for the step lengths 47/53/43/53/47
exactly — `53-47 = 17-11 = 6` and `47-43 = 11-7 = 4`.  Nothing else in a round
varies by group, so a bridge parameterised on the `f` shape covers the group
index completely.

STATUS: WRITTEN, NOT ELABORATED.  No admitted goals; the file contains zero
occurrences of the placeholder token, so a grep and this claim agree.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepOrder

open EvmSemantics
open Challenge.EvmProof.Word

/-! ## 0.  Commutativity of the four operators, on the notation the certificate
produces.  `Bytecode.Word` has `land_comm` / `lor_comm` but states them on
`UInt256.land` / `UInt256.lor`; there is no `xor` or `add` counterpart, so all
four are given here in the `&&&` / `|||` / `^^^` / `+` forms that the emitted
expressions actually use. -/

private theorem toNat_lxor (a b : UInt256) :
    (a ^^^ b).toNat = a.toNat ^^^ b.toNat := by
  change (a.toNat ^^^ b.toNat) % UInt256.size = _
  rw [show UInt256.size = 2 ^ 256 from rfl]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.val.isLt b.val.isLt)

theorem uand_comm (a b : UInt256) : a &&& b = b &&& a := by
  apply word_ext
  change (UInt256.land a b).toNat = (UInt256.land b a).toNat
  rw [word_toNat_land, word_toNat_land, Nat.and_comm]

theorem uor_comm (a b : UInt256) : a ||| b = b ||| a := by
  apply word_ext
  change (UInt256.lor a b).toNat = (UInt256.lor b a).toNat
  rw [word_toNat_lor, word_toNat_lor, Nat.or_comm]

theorem uxor_comm (a b : UInt256) : a ^^^ b = b ^^^ a := by
  apply word_ext
  rw [toNat_lxor, toNat_lxor, Nat.xor_comm]

theorem uadd_comm (a b : UInt256) : a + b = b + a := by
  apply word_ext
  rw [word_toNat_add, word_toNat_add, Nat.add_comm]

/-! ## The six conversions, emitted order on the left -/

/-- **1. Message word.**  The round loads the RIGHT lane first, so the `OR`
comes out with the lane-1 word on the left. -/
theorem load_order (xLeft xRight : UInt256) :
    xRight ||| xLeft = xLeft ||| xRight :=
  uor_comm xRight xLeft

/-- **2. Packed `f` at `r = 0`** (the blend shape, shared with `r = 4`).
Five commutations, no reassociation. -/
theorem f0_order (b c d mR : UInt256) :
    (d ||| (mR &&& c)) ^^^ (mR ^^^ (c ^^^ b))
      = ((b ^^^ c) ^^^ mR) ^^^ ((c &&& mR) ||| d) := by
  rw [uand_comm mR c, uor_comm d (c &&& mR), uxor_comm c b,
    uxor_comm mR (b ^^^ c), uxor_comm ((c &&& mR) ||| d) ((b ^^^ c) ^^^ mR)]

/-- **3. Round sum.**  `DUP16` lifts the constant, so the last `ADD` has it on
the left.  One `add_comm`; the inner `(f + X) + a` already matches. -/
theorem sum_order (k s : UInt256) : k + s = s + k :=
  uadd_comm k s

/-- **4. Rotate.**  Both the outer `|||` and each inner `&&&` come out
reversed: the mask is on the left in the emitted form. -/
theorem rot_order (qsl qsr mL mR : UInt256) :
    (mR &&& qsr) ||| (mL &&& qsl) = (qsl &&& mL) ||| (qsr &&& mR) := by
  rw [uand_comm mR qsr, uand_comm mL qsl,
    uor_comm (qsr &&& mR) (qsl &&& mL)]

/-- **5. Write-back.**  The rotation result is added to `e` with `e` on the
left. -/
theorem writeback_order (e rot : UInt256) : e + rot = rot + e :=
  uadd_comm e rot

/-- **6. `rol10`.**  Two `and_comm`s — the outer mask and the inner one.  The
multiplication is already in the definition's order, so it is untouched. -/
theorem rol10_order (mLR c cM u : UInt256) :
    mLR &&& UInt256.shiftRight (cM * (mLR &&& c)) u
      = UInt256.shiftRight (cM * (c &&& mLR)) u &&& mLR := by
  rw [uand_comm mLR c,
    uand_comm mLR (UInt256.shiftRight (cM * (c &&& mLR)) u)]

/-! ## The other two `f` shapes

Decoded from the artifact, not extrapolated from group 0: the select shape has
a nested `AND`/`OR` the blend shape does not, and the short shape uses `OR`
where the others use `AND`. -/

/-- **The select shape** (groups 1 and 3, 17 ops).  The correction term
`(b,c,d,m)` is shared by both groups; the base `(p,q,r)` distinguishes them —
group 1 instantiates `(p,q,r) := (B,C,D)` and group 3 `(p,q,r) := (D,B,C)`,
with `(b,c,d) := (B,C,D)` in both.  Eight commutations, no reassociation. -/
theorem fSelect_order (p q r b c d m : UInt256) :
    (m &&& ((d ||| c) ^^^ (c &&& b))) ^^^ (r ^^^ (p &&& (r ^^^ q)))
      = (((q ^^^ r) &&& p) ^^^ r) ^^^ (((b &&& c) ^^^ (c ||| d)) &&& m) := by
  rw [uor_comm d c, uand_comm c b, uxor_comm (c ||| d) (b &&& c),
    uand_comm m ((b &&& c) ^^^ (c ||| d)), uxor_comm r q,
    uand_comm p (q ^^^ r), uxor_comm r (((q ^^^ r) &&& p)),
    uxor_comm ((((b &&& c) ^^^ (c ||| d)) &&& m))
      ((((q ^^^ r) &&& p) ^^^ r))]

/-- **The short shape** (group 2, 7 ops).  Three commutations. -/
theorem fShort_order (b c d m : UInt256) :
    d ^^^ (b ||| (m ^^^ c)) = ((c ^^^ m) ||| b) ^^^ d := by
  rw [uxor_comm m c, uor_comm b (c ^^^ m), uxor_comm d ((c ^^^ m) ||| b)]

/-- `f0_order` also covers group 4: the mask argument is abstract, so
instantiating it at `maskL` instead of `maskR` gives the group-4 conversion
with no new lemma. -/
theorem f4_order (b c d mL : UInt256) :
    (d ||| (mL &&& c)) ^^^ (mL ^^^ (c ^^^ b))
      = ((b ^^^ c) ^^^ mL) ^^^ ((c &&& mL) ||| d) :=
  f0_order b c d mL

#print axioms fSelect_order
#print axioms fShort_order
#print axioms f4_order
#print axioms uand_comm
#print axioms uor_comm
#print axioms uxor_comm
#print axioms uadd_comm
#print axioms load_order
#print axioms f0_order
#print axioms sum_order
#print axioms rot_order
#print axioms writeback_order
#print axioms rol10_order

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepOrder
