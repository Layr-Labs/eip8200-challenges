import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBridge

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Assembling a round's bridge

`PackedBridge`'s six equalities are proved.  A round's bridge is two live slots,
so this module is two lemmas — and each is split again so that every rewrite has
a SMALL instantiation.

That split is the whole technique here.  Written in one piece, slot 2's
`rot_order` rewrite would have to be given a four-hundred-character explicit
argument, and getting one parenthesis wrong produces an error far from the
cause.  Abstracting the round sum to a variable `S` first makes the outer
rewrite's operands two short terms, and the inner equality is then a separate
lemma over the sum alone.  Neither half mentions the other.

Three things had to be reconciled in `slot2_outer`, and only ONE of them was a
real commutation:

* `maskLR &&& S` against `S &&& maskLR` — genuinely different, and `uand_comm`
  performs it;
* `cMul * _` against `UInt256.mul cMul _`, and `|||`/`&&&` against
  `UInt256.lor`/`.land` — the same terms with different heads after
  elaboration, which `rw` will not match through;
* `UInt256.ofNat 24` against `UInt256.ofNat (32 - 8)` — the shift arrives in
  its derived form because that is what `shiftSupply` computes.

The last two are definitional, so a single `have … := rfl` normalises both
heads and both numerals in one step and leaves only the commutation.  Fighting
them with `rw` would have needed a pattern in exactly the elaborated form,
which is brittle against any change in how the notation resolves.  Keeping the
derived `32 - s` form in mind matters for the parameterised template, which will
always carry it symbolically.

**The two loaded words are parameters, not `memAt` applications.**  `PUSH0`
produces the `OfNat` literal `0` while `roundSum` is written with
`UInt256.ofNat 0`; the same value in two syntactic forms, and `rw` will not
match through it.  Abstracting both words removes that mismatch entirely
instead of normalising one instance of it — which matters because `PUSH0` fires
at rounds 0, 25, 42, 52 and 65, so the form difference recurs.

`simp only` with these lemmas is NOT an option and the reason is worth
recording: `sum_order`, `writeback_order` and `load_order` are commutativity
statements, and simp will rewrite with them in both directions and loop.  Every
step below is an explicit `rw` with its operands named.

STATUS: WRITTEN, NOT ELABORATED.  Axiom status unknown until built.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAssembly

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepOrder
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBridge

/-- Slot 4, the new `d`.  One order rewrite, at the round's own operands. -/
theorem slot4 (sf : Suffix) (hstd : FrameStd sf) (c : UInt256) :
    sf.maskLRv &&& UInt256.shiftRight (sf.cMulv * (sf.maskLRv &&& c)) sf.s22
      = packedRol10 c :=
  bridge_rol10 sf hstd c

/-- Slot 2, inner half: the emitted round sum is `roundSum`.  The message word,
the packed `f`, and the constant's position, in that order. -/
theorem slot2_inner (sf : Suffix) (hstd : FrameStd sf)
    (a b c d e X0 X88 : UInt256) :
    sf.konst + ((((d ||| (sf.maskRv &&& c)) ^^^ (sf.maskRv ^^^ (c ^^^ b)))
        + (X88 ||| X0)) + a)
      = roundSum 0 { a := a, b := b, c := c, d := d, e := e }
          (X0 ||| X88) sf.konst := by
  unfold roundSum
  rw [hstd.mR, load_order X0 X88, f0_order b c d maskR]
  exact sum_order _ _

/-- Slot 2, outer half: with the sum abstracted, the emitted rotate-and-add is
`packedRot … + e`.  Two order rewrites, both with short operands. -/
theorem slot2_outer (sf : Suffix) (hstd : FrameStd sf) (S e : UInt256) :
    e + ((sf.maskRv &&& UInt256.shiftRight (sf.cMulv * (sf.maskLRv &&& S))
            (UInt256.ofNat 24))
        ||| (sf.maskLv &&& UInt256.shiftRight (sf.cMulv * (sf.maskLRv &&& S))
            sf.s21))
      = packedRot S 11 8 + e := by
  rw [hstd.mR, hstd.mL, hstd.mLR, hstd.cM, hstd.h21]
  -- `packedRot` is written with `UInt256.lor` / `.land` / `.mul` and an
  -- unreduced `32 - 11`; the emitted side uses the notations and a literal.
  -- Those are all definitional, so one `rfl` bridges the heads and the numerals
  -- at once and leaves only the genuine commutation to perform.
  have hpr : packedRot S 11 8
      = (UInt256.shiftRight (cMul * (S &&& maskLR)) (UInt256.ofNat 21)
          &&& maskL)
        ||| (UInt256.shiftRight (cMul * (S &&& maskLR)) (UInt256.ofNat 24)
          &&& maskR) := rfl
  rw [hpr, uand_comm maskLR S]
  rw [rot_order
      (UInt256.shiftRight (cMul * (S &&& maskLR)) (UInt256.ofNat 21))
      (UInt256.shiftRight (cMul * (S &&& maskLR)) (UInt256.ofNat 24))
      maskL maskR]
  exact writeback_order e _

/-- Slot 2, whole: the inner equality rewritten under the outer one. -/
theorem slot2 (sf : Suffix) (hstd : FrameStd sf)
    (a b c d e X0 X88 : UInt256) :
    e + ((sf.maskRv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& (sf.konst
              + ((((d ||| (sf.maskRv &&& c)) ^^^ (sf.maskRv ^^^ (c ^^^ b)))
                  + (X88 ||| X0))
                + a))))
            (UInt256.ofNat 24))
        ||| (sf.maskLv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& (sf.konst
              + ((((d ||| (sf.maskRv &&& c)) ^^^ (sf.maskRv ^^^ (c ^^^ b)))
                  + (X88 ||| X0))
                + a))))
            sf.s21))
      = packedRot
          (roundSum 0 { a := a, b := b, c := c, d := d, e := e }
            (X0 ||| X88) sf.konst)
          11 8 + e := by
  rw [slot2_inner sf hstd a b c d e X0 X88]
  exact slot2_outer sf hstd _ e

#print axioms slot4
#print axioms slot2_inner
#print axioms slot2_outer
#print axioms slot2

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAssembly
