import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplates

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The remaining eight round templates

One per (phase, group) class not already covered by `PackedTemplates`, each
stated over `emitRound` with the phase and index as literals, and each checked
against the machine before being written down — executor run from the real entry
stack and real memory at that round, exit stack compared in all nineteen slots.
Round 0 was re-run as the control on the same pass, as it has been throughout.

Representative rounds were chosen to avoid the five `PUSH0` indices where a
class had an alternative: even/group 0 uses round 2 rather than 0, and
odd/group 4 uses round 67 rather than 65.  With `pushOffset` deriving the opcode
this no longer changes the lemma's truth, but it keeps each template
representative of its class at a glance.

## If `rfl` will not unfold the schedule tables

That risk is named in `PackedTemplates` and the fix is uniform, not per-lemma.
Each template here is paired with an `emitRound_eq_i` length lemma over the same
`emitRound` application.  Those are the isolation points: they exercise the
table unfolding and nothing else, so a first elaboration tells us immediately
whether the problem is the schedule lookup or the forty-odd operation
evaluation.  If it is the lookup, only the ten small lemmas need a different
proof — `decide`, or `simp [emitRound, roundBody, pushOffset, shiftSupply]` —
and the ten templates are then restated against the pinned lists without
touching their statements.

## Ten templates are not eighty rounds — the scaling step, and it is available

Each template here is specific to one index, because `emitRound i` bakes in that
round's offsets and shift amounts.  Ten of them do not cover eighty rounds.

The step that does is available and cheap, and it turns on a fact I checked
rather than assumed: the six resident shift slots hold exactly `17 … 22`
        (measured at round-0 entry).  Given that, BOTH branches of `shiftSupply` have
the same effect — the `push` branch pushes `v`, and the `dup` branch duplicates
the slot that holds `v`.  So a template parameterised on the two shift VALUES
and the two offsets, rather than on the index, covers all eight rounds of its
class, and ten such lemmas cover all eighty.  That needs a `SuffixStd` premise
pinning the resident slots, which is a real hypothesis with a real failure mode
— a frame whose shift slots held anything else would break it.

STATUS: WRITTEN, NOT ELABORATED.  No admitted goals; the file contains zero
occurrences of the placeholder token, so a grep and this claim agree.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplatesRest

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit

/-- Round 2: even phase, group 0, 47 operations. -/
theorem round2_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (emitRound Phase.even 2)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (e :: b :: (e + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((d
         ||| (mR &&& c)) ^^^ (mR ^^^ (c ^^^ b))) + ((memAt
         (UInt256.ofNat 120)) ||| (memAt (UInt256.ofNat 32)))) + a))))
         (UInt256.ofNat 23))) ||| (mL &&& (UInt256.shiftRight (cM * (mLR
         &&& (kk + ((((d ||| (mR &&& c)) ^^^ (mR ^^^ (c ^^^ b))) +
         ((memAt (UInt256.ofNat 120)) ||| (memAt (UInt256.ofNat 32)))) +
         a)))) u17)))) :: d :: (mLR &&& (UInt256.shiftRight (cM * (mLR
         &&& c)) u22)) :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest) := rfl

/-- Isolation point for round 2: if the kernel will not unfold the schedule
tables, this is the lemma that fails, and only its proof changes. -/
theorem emitRound_eq_2 :
    (emitRound Phase.even 2).length = 47 := rfl

/-- Round 16: even phase, group 1, 53 operations. -/
theorem round16_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (emitRound Phase.even 16)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (e :: b :: (e + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((mR
         &&& ((d ||| c) ^^^ (c &&& b))) ^^^ (d ^^^ (b &&& (d ^^^ c)))) +
         ((memAt (UInt256.ofNat 104)) ||| (memAt (UInt256.ofNat 112))))
         + a)))) (UInt256.ofNat 23))) ||| (mL &&& (UInt256.shiftRight
         (cM * (mLR &&& (kk + ((((mR &&& ((d ||| c) ^^^ (c &&& b))) ^^^
         (d ^^^ (b &&& (d ^^^ c)))) + ((memAt (UInt256.ofNat 104)) |||
         (memAt (UInt256.ofNat 112)))) + a)))) (UInt256.ofNat 25))))) ::
         d :: (mLR &&& (UInt256.shiftRight (cM * (mLR &&& c)) u22)) ::
         mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 :: u20 :: u21 :: u22
         :: kk :: ret :: xo :: xe :: rest) := rfl

/-- Isolation point for round 16: if the kernel will not unfold the schedule
tables, this is the lemma that fails, and only its proof changes. -/
theorem emitRound_eq_16 :
    (emitRound Phase.even 16).length = 53 := rfl

/-- Round 17: odd phase, group 1, 53 operations. -/
theorem round17_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (emitRound Phase.odd 17)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (d :: (d + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((mR &&&
         ((e ||| b) ^^^ (b &&& c))) ^^^ (e ^^^ (c &&& (e ^^^ b)))) +
         ((memAt (UInt256.ofNat 184)) ||| (memAt (UInt256.ofNat 64)))) +
         a)))) u19)) ||| (mL &&& (UInt256.shiftRight (cM * (mLR &&& (kk
         + ((((mR &&& ((e ||| b) ^^^ (b &&& c))) ^^^ (e ^^^ (c &&& (e
         ^^^ b)))) + ((memAt (UInt256.ofNat 184)) ||| (memAt
         (UInt256.ofNat 64)))) + a)))) (UInt256.ofNat 26))))) :: c ::
         (mLR &&& (UInt256.shiftRight (cM * (mLR &&& b)) u22)) :: e ::
         mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 :: u20 :: u21 :: u22
         :: kk :: ret :: xo :: xe :: rest) := rfl

/-- Isolation point for round 17: if the kernel will not unfold the schedule
tables, this is the lemma that fails, and only its proof changes. -/
theorem emitRound_eq_17 :
    (emitRound Phase.odd 17).length = 53 := rfl

/-- Round 33: odd phase, group 2, 43 operations. -/
theorem round33_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (emitRound Phase.odd 33)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (d :: (d + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + (((e ^^^ (c
         ||| (mLR ^^^ b))) + ((memAt (UInt256.ofNat 88)) ||| (memAt
         (UInt256.ofNat 160)))) + a)))) (UInt256.ofNat 25))) ||| (mL &&&
         (UInt256.shiftRight (cM * (mLR &&& (kk + (((e ^^^ (c ||| (mLR
         ^^^ b))) + ((memAt (UInt256.ofNat 88)) ||| (memAt
         (UInt256.ofNat 160)))) + a)))) u19)))) :: c :: (mLR &&&
         (UInt256.shiftRight (cM * (mLR &&& b)) u22)) :: e :: mLR :: mL
         :: mR :: cM :: u17 :: u18 :: u19 :: u20 :: u21 :: u22 :: kk ::
         ret :: xo :: xe :: rest) := rfl

/-- Isolation point for round 33: if the kernel will not unfold the schedule
tables, this is the lemma that fails, and only its proof changes. -/
theorem emitRound_eq_33 :
    (emitRound Phase.odd 33).length = 43 := rfl

/-- Round 48: even phase, group 3, 53 operations. -/
theorem round48_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (emitRound Phase.even 48)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (e :: b :: (e + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((mR
         &&& ((d ||| c) ^^^ (c &&& b))) ^^^ (c ^^^ (d &&& (c ^^^ b)))) +
         ((memAt (UInt256.ofNat 136)) ||| (memAt (UInt256.ofNat 16)))) +
         a)))) u17)) ||| (mL &&& (UInt256.shiftRight (cM * (mLR &&& (kk
         + ((((mR &&& ((d ||| c) ^^^ (c &&& b))) ^^^ (c ^^^ (d &&& (c
         ^^^ b)))) + ((memAt (UInt256.ofNat 136)) ||| (memAt
         (UInt256.ofNat 16)))) + a)))) u21)))) :: d :: (mLR &&&
         (UInt256.shiftRight (cM * (mLR &&& c)) u22)) :: mLR :: mL :: mR
         :: cM :: u17 :: u18 :: u19 :: u20 :: u21 :: u22 :: kk :: ret ::
         xo :: xe :: rest) := rfl

/-- Isolation point for round 48: if the kernel will not unfold the schedule
tables, this is the lemma that fails, and only its proof changes. -/
theorem emitRound_eq_48 :
    (emitRound Phase.even 48).length = 53 := rfl

/-- Round 49: odd phase, group 3, 53 operations. -/
theorem round49_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (emitRound Phase.odd 49)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (d :: (d + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((mR &&&
         ((e ||| b) ^^^ (b &&& c))) ^^^ (b ^^^ (e &&& (b ^^^ c)))) +
         ((memAt (UInt256.ofNat 104)) ||| (memAt (UInt256.ofNat 144))))
         + a)))) (UInt256.ofNat 27))) ||| (mL &&& (UInt256.shiftRight
         (cM * (mLR &&& (kk + ((((mR &&& ((e ||| b) ^^^ (b &&& c))) ^^^
         (b ^^^ (e &&& (b ^^^ c)))) + ((memAt (UInt256.ofNat 104)) |||
         (memAt (UInt256.ofNat 144)))) + a)))) u20)))) :: c :: (mLR &&&
         (UInt256.shiftRight (cM * (mLR &&& b)) u22)) :: e :: mLR :: mL
         :: mR :: cM :: u17 :: u18 :: u19 :: u20 :: u21 :: u22 :: kk ::
         ret :: xo :: xe :: rest) := rfl

/-- Isolation point for round 49: if the kernel will not unfold the schedule
tables, this is the lemma that fails, and only its proof changes. -/
theorem emitRound_eq_49 :
    (emitRound Phase.odd 49).length = 53 := rfl

/-- Round 64: even phase, group 4, 47 operations. -/
theorem round64_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (emitRound Phase.even 64)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (e :: b :: (e + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((d
         ||| (mL &&& c)) ^^^ (mL ^^^ (c ^^^ b))) + ((memAt
         (UInt256.ofNat 200)) ||| (memAt (UInt256.ofNat 64)))) + a))))
         (UInt256.ofNat 24))) ||| (mL &&& (UInt256.shiftRight (cM * (mLR
         &&& (kk + ((((d ||| (mL &&& c)) ^^^ (mL ^^^ (c ^^^ b))) +
         ((memAt (UInt256.ofNat 200)) ||| (memAt (UInt256.ofNat 64)))) +
         a)))) (UInt256.ofNat 23))))) :: d :: (mLR &&&
         (UInt256.shiftRight (cM * (mLR &&& c)) u22)) :: mLR :: mL :: mR
         :: cM :: u17 :: u18 :: u19 :: u20 :: u21 :: u22 :: kk :: ret ::
         xo :: xe :: rest) := rfl

/-- Isolation point for round 64: if the kernel will not unfold the schedule
tables, this is the lemma that fails, and only its proof changes. -/
theorem emitRound_eq_64 :
    (emitRound Phase.even 64).length = 47 := rfl

/-- Round 67: odd phase, group 4, 47 operations. -/
theorem round67_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (emitRound Phase.odd 67)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (d :: (d + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((e |||
         (mL &&& b)) ^^^ (mL ^^^ (b ^^^ c))) + ((memAt (UInt256.ofNat
         72)) ||| (memAt (UInt256.ofNat 144)))) + a)))) (UInt256.ofNat
         23))) ||| (mL &&& (UInt256.shiftRight (cM * (mLR &&& (kk +
         ((((e ||| (mL &&& b)) ^^^ (mL ^^^ (b ^^^ c))) + ((memAt
         (UInt256.ofNat 72)) ||| (memAt (UInt256.ofNat 144)))) + a))))
         u21)))) :: c :: (mLR &&& (UInt256.shiftRight (cM * (mLR &&& b))
         u22)) :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 :: u20
         :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest) := rfl

/-- Isolation point for round 67: if the kernel will not unfold the schedule
tables, this is the lemma that fails, and only its proof changes. -/
theorem emitRound_eq_67 :
    (emitRound Phase.odd 67).length = 47 := rfl

#print axioms round2_template
#print axioms round16_template
#print axioms round17_template
#print axioms round33_template
#print axioms round48_template
#print axioms round49_template
#print axioms round64_template
#print axioms round67_template

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplatesRest
