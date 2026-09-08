import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Round 0 as a symbolic template — concrete control, symbolic data

`PackedStep0.step0_trace` fixes the nineteen frame slots as named variables but
ends the stack there.  This file is the version the fold can actually consume:
the operation list and the stack SHAPE are concrete, and everything else — the
five registers, the fourteen suffix slots, the memory, and the tail `rest`
below the frame — is universally quantified.

`rest` matters.  `DUP16` reaches index 15 and no operation in round 0 reaches
deeper, so the round inspects only the nineteen-slot concrete prefix and leaves
whatever is beneath it untouched.  Stating the lemma over `… :: rest` from the
start is what lets one round's conclusion be another round's hypothesis; a
lemma that pinned the stack to exactly nineteen elements would not compose.

## The reduction question, answered

The interpreter here is **unchecked**: `PackedStep0.runOp` guards nothing on
gas, on stack depth, or on `msize`.  It matches on the stack shape and computes.
So symbolic evaluation does not get stuck — with the frame written as nineteen
explicit `::` cells over an abstract tail, every `dup`, `swap` and binary step
reduces, and `rest` is never inspected.  That is why this lemma can be `rfl`
with the data symbolic.

The guard problem the strategic note anticipates is real, but it lives at the
boundary to the framework's *checked* stepper, not here.  Discharging it is the
refinement lemma — checked equals unchecked when gas covers the total cost, the
depth stays under the limit, and memory is already expanded — and that lemma is
about the op whitelist, so it is proved once for all eighty rounds rather than
per template.  This file is the "unchecked pure executor" half of that plan,
and it is the half that reduces.

STATUS: WRITTEN, NOT ELABORATED.  No admitted goals; the file contains zero
occurrences of the placeholder token, so a grep and this claim agree.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0Template

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0

/-- **The template.**  Concrete control, symbolic data: the forty-seven ops and
the nineteen-slot shape are fixed, the contents and the tail are not. -/
theorem step0_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256)
    (rest : List UInt256) :
    runOps memAt step0Ops
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (e :: b :: (e + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((d
         ||| (mR &&& c)) ^^^ (mR ^^^ (c ^^^ b))) + ((memAt
         (UInt256.ofNat 88)) ||| (memAt (0 : UInt256)))) + a))))
         (UInt256.ofNat 24))) ||| (mL &&& (UInt256.shiftRight (cM * (mLR
         &&& (kk + ((((d ||| (mR &&& c)) ^^^ (mR ^^^ (c ^^^ b))) +
         ((memAt (UInt256.ofNat 88)) ||| (memAt (0 : UInt256)))) + a))))
         u21)))) :: d :: (mLR &&& (UInt256.shiftRight (cM * (mLR &&& c))
         u22)) :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 :: u20 ::
         u21 :: u22 :: kk :: ret :: xo :: xe :: rest) := rfl

/-- The tail below the frame is untouched, and it is untouched *because* no
operation reaches past index 15, not because it was assumed absent. -/
theorem step0_rest (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256)
    (rest : List UInt256) :
    (runOps memAt step0Ops
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)).map (List.drop 19)
      = some rest := rfl

/-- The frame shape composes: nineteen in, nineteen out, tail preserved, so one
round's conclusion is the next round's hypothesis. -/
theorem step0_frame_shape (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256)
    (rest : List UInt256) :
    (runOps memAt step0Ops
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)).map
        (fun t => (t.take 19).length)
      = some 19 := rfl

/-- Written as `regsStack ++ suffixStack ++ rest`, which is the form the fold
uses.  Definitionally the same nineteen cells. -/
theorem step0_layout_form
    (a b c d e : UInt256) (sf : Suffix) (rest : List UInt256) :
    regsStack Phase.even ⟨a, b, c, d, e⟩ ++ suffixStack sf ++ rest
      = a :: b :: c :: d :: e :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
        sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 ::
        sf.s22 :: sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl

#print axioms step0_template
#print axioms step0_rest
#print axioms step0_frame_shape
#print axioms step0_layout_form

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0Template
