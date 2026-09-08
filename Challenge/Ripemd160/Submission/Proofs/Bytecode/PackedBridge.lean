import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepOrder

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# From an execution template to `correctedStep`

A template says what the machine leaves on the stack.  `correctedStep` says what
the arithmetic layer proved about.  This module joins them.

## The join is two element equalities, not nineteen

At round 0 the template's output is `[e, b, T, d, rol10]` and
`regsStack .odd (correctedStep …)` is `[E, B, T, D, rol10 C]`, which in the
entry variables is `[e, b, T, d, rol10 c]`.  Slots 0, 1 and 3 are pure register
moves and already agree; the fourteen suffix slots and the tail are untouched.
So the whole content of a round's bridge is the two computed values — the new
`b` and the new `d` — and everything else is structural.

That is why the eleven order rewrites are enough: five of them live inside the
new `b`, one inside the new `d`, and there is nothing else to convert.

## What `FrameStd` pins, and why it can fail

The template carries the masks, the multiplier and the six rotation constants
as opaque stack variables, because that is what they are on the machine.  The
arithmetic layer names them.  `FrameStd` is the statement that the frame's
slots hold the values the arithmetic layer expects.

It is falsifiable in the same concrete way `SuffixStd` is: a frame whose
`maskRv` slot held something other than `maskR` would make the emitted `f`
compute a different function, and the bridge would be false rather than
unprovable.  It is not a bookkeeping premise.

STATUS: WRITTEN, NOT ELABORATED.  Axiom status unknown until built.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBridge

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepOrder
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric

/-- The frame's constant slots hold the values the arithmetic layer names.
Falsifiable: a wrong mask makes the emitted `f` a different function. -/
structure FrameStd (sf : Suffix) : Prop where
  mLR : sf.maskLRv = maskLR
  mL : sf.maskLv = maskL
  mR : sf.maskRv = maskR
  cM : sf.cMulv = cMul
  h21 : sf.s21 = UInt256.ofNat 21
  h22 : sf.s22 = UInt256.ofNat 22

/-! ## The two computed slots, one lemma each

Each is stated in the direction the template produces, so it rewrites forward
into the arithmetic layer's form. -/

/-- The new `d` slot: the emitted `rol10` is `packedRol10`.  One order lemma. -/
theorem bridge_rol10 (sf : Suffix) (hstd : FrameStd sf) (c : UInt256) :
    sf.maskLRv &&& UInt256.shiftRight (sf.cMulv * (sf.maskLRv &&& c)) sf.s22
      = packedRol10 c := by
  rw [hstd.mLR, hstd.cM, hstd.h22]
  exact rol10_order maskLR c cMul (UInt256.ofNat 22)

/-- The message word: the round loads the right lane first. -/
theorem bridge_X (memAt : UInt256 → UInt256) (lo hi : UInt256) :
    memAt hi ||| memAt lo = memAt lo ||| memAt hi :=
  load_order (memAt lo) (memAt hi)

/-- The packed `f` at the blend shape. -/
theorem bridge_f0 (sf : Suffix) (hstd : FrameStd sf) (b c d : UInt256) :
    (d ||| (sf.maskRv &&& c)) ^^^ (sf.maskRv ^^^ (c ^^^ b))
      = Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFBridge.packedFWord
          0 b c d := by
  rw [hstd.mR]
  exact f0_order b c d maskR

/-- The round sum: `DUP16` lifts the constant, so the last `ADD` has it on the
left. -/
theorem bridge_sum (k s : UInt256) : k + s = s + k :=
  sum_order k s

/-- The rotate: mask on the left in the emitted form, and the two lanes in the
other order. -/
theorem bridge_rot (sf : Suffix) (hstd : FrameStd sf) (qsl qsr : UInt256) :
    (sf.maskRv &&& qsr) ||| (sf.maskLv &&& qsl)
      = (qsl &&& maskL) ||| (qsr &&& maskR) := by
  rw [hstd.mR, hstd.mL]
  exact rot_order qsl qsr maskL maskR

/-- The write-back: the rotation result is added to `e` with `e` on the left. -/
theorem bridge_writeback (e rot : UInt256) : e + rot = rot + e :=
  writeback_order e rot

/-! ## What remains, stated so it cannot be mistaken for done

The six lemmas above convert every emitted sub-expression into the arithmetic
layer's form.  Assembling them into

    runOps memAt (emitRound Phase.even 0) (frameStack f)
      = some (frameStack (stepFrame 0 s sP X f))

is a congruence over the two computed slots, using `step0_template` for the
left-hand side.  I have deliberately not written that assembly until these six
elaborate: they are the content, the assembly is bookkeeping over them, and if
one of the six fails the assembly built on it would fail in a way that hides
which. -/

#print axioms bridge_rol10
#print axioms bridge_X
#print axioms bridge_f0
#print axioms bridge_sum
#print axioms bridge_rot
#print axioms bridge_writeback

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBridge
