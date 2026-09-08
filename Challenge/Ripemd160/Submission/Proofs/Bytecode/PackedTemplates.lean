import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Two template lemmas, chosen to test the two axes separately

Round 1 is odd phase, group 0 — it differs from the proved round-0 template
only in phase.  Round 32 is even phase, group 2 — the short `f` shape and the
shortest body.  Between them they exercise the phase axis and the `f`-shape
axis independently, so if both reduce the remaining eight are mechanical.

## These are stated over `emitRound`, not over transcribed lists

The op list in each statement is `emitRound Phase.odd 1` and
`emitRound Phase.even 32`.  Both reduce, because the phase and the index are
literals: `roundBody` picks its branch, `pushOffset` computes from `r`/`rP`, and
`shiftSupply` computes from `s`/`sP`.  So these lemmas are about what the
emitter produces, and a change to `PackedEmit` that broke the offsets or the
shift rule would break them — which a transcribed list would not.

That is also the one reduction risk worth naming: `rfl` here has to unfold the
table lookups as well as the forty-odd operations, where round 0's template
only had to unfold a literal list.  If the kernel balks, the fix is to pin the
list with an auxiliary `emitRound Phase.odd 1 = [...]` step proved by `decide`
or `simp` and then reuse round 0's shape — not to abandon the `emitRound`
formulation.

## No `hcap` here, deliberately

`§2.4`'s `hcap : rest.length < K` threading belongs at the framework's checked
`runInstr`, whose single guard is `s.stack.length < 1024`.  `runOps` is the
unchecked executor and guards nothing, so a depth hypothesis on these lemmas
would constrain nothing and could not fail.  It enters one level up, at the
`runLocatedBlock` boundary, and I have not smuggled it down here to look
thorough.

STATUS: WRITTEN, NOT ELABORATED.  No admitted goals; the file contains zero
occurrences of the placeholder token, so a grep and this claim agree.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplates

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit

/-- Round 1: odd phase, group 0.  Same body shape as round 0, transposed
register depths, and the rotation slots filled from `s[1]` / `sP[1]`. -/
theorem round1_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (emitRound Phase.odd 1)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (d :: (d + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((e |||
         (mR &&& b)) ^^^ (mR ^^^ (b ^^^ c))) + ((memAt (UInt256.ofNat
         232)) ||| (memAt (UInt256.ofNat 16)))) + a)))) (UInt256.ofNat
         23))) ||| (mL &&& (UInt256.shiftRight (cM * (mLR &&& (kk +
         ((((e ||| (mR &&& b)) ^^^ (mR ^^^ (b ^^^ c))) + ((memAt
         (UInt256.ofNat 232)) ||| (memAt (UInt256.ofNat 16)))) + a))))
         u18)))) :: c :: (mLR &&& (UInt256.shiftRight (cM * (mLR &&& b))
         u22)) :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 :: u20
         :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest) := rfl

/-- Round 32: even phase, group 2.  The short `f` shape — 43 operations, the
shortest round in the artifact. -/
theorem round32_template (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (emitRound Phase.even 32)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)
      = some
        (e :: b :: (e + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + (((d
         ^^^ (b ||| (mLR ^^^ c))) + ((memAt (UInt256.ofNat 248)) |||
         (memAt (UInt256.ofNat 48)))) + a)))) (UInt256.ofNat 23))) |||
         (mL &&& (UInt256.shiftRight (cM * (mLR &&& (kk + (((d ^^^ (b
         ||| (mLR ^^^ c))) + ((memAt (UInt256.ofNat 248)) ||| (memAt
         (UInt256.ofNat 48)))) + a)))) u21)))) :: d :: (mLR &&&
         (UInt256.shiftRight (cM * (mLR &&& c)) u22)) :: mLR :: mL :: mR
         :: cM :: u17 :: u18 :: u19 :: u20 :: u21 :: u22 :: kk :: ret ::
         xo :: xe :: rest) := rfl

/-- Both rounds leave the fourteen-slot suffix and the tail untouched. -/
theorem round1_suffix (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    (runOps memAt (emitRound Phase.odd 1)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)).map (List.drop 5)
      = some (mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 :: u20 :: u21 ::
          u22 :: kk :: ret :: xo :: xe :: rest) := rfl

theorem round32_suffix (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) (rest : List UInt256) :
    (runOps memAt (emitRound Phase.even 32)
        (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 ::
         u20 :: u21 :: u22 :: kk :: ret :: xo :: xe :: rest)).map (List.drop 5)
      = some (mLR :: mL :: mR :: cM :: u17 :: u18 :: u19 :: u20 :: u21 ::
          u22 :: kk :: ret :: xo :: xe :: rest) := rfl

/-- The emitted lengths, matching the measured group lengths. -/
theorem round1_length : (emitRound Phase.odd 1).length = 47 := rfl

theorem round32_length : (emitRound Phase.even 32).length = 43 := rfl

#print axioms round1_template
#print axioms round32_template
#print axioms round1_suffix
#print axioms round32_suffix
#print axioms round1_length
#print axioms round32_length

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplates
