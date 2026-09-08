import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeCut

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 80000
set_option maxHeartbeats 4000000

/-!
# The composition probe, assembled

Group 2, even phase, over abstract offsets and abstract rotation amounts - the
first template stated over a round's DATA rather than its index, so it covers
all eight rounds of its class.

## How it avoids the two failures that got us here

No `simp`.  The proof is nine rewrites: four peels of a symbolic opcode using
its effect lemma, four peels of a concrete stretch using `rfl`, and the cut that
regroups the list.  Every concrete stretch is reduced by the KERNEL, which has
no difficulty with the literal `DUP` indices that a named `simp only` set cannot
touch for want of a simproc, and that a default `simp` set could only reach by a
search that cost 6 GB.

No `Option` lemma by name either: `runOps_cons_effect` and `runOps_seg` both
make the bind visible with a `show` and let it reduce after rewriting the known
effect.  That matters because two assumed-by-analogy names have already cost
builds here.

## Where each intermediate stack comes from

Nowhere - none is written.  Each peel's resulting stack is inferred: for a
concrete stretch `rfl` forces `runOps memAt seg s` to whnf and unification reads
`some t` off it, and for a symbolic opcode the effect lemma supplies `t`
directly.  That is the whole reason the file is short.

STATUS: WRITTEN, NOT ELABORATED.  Axiom status unknown until built.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeExec

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbe
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeCut

/-- **The composition probe.**  Group 2, even phase, parameterised on the two
message offsets and the two rotation amounts. -/
theorem bodyEven2_exec (memAt : UInt256 → UInt256) (lo hi vl vr : Nat)
    (a b c d e mLR mL mR cM kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload ::
      Op.or :: bodyEven2 (shiftSupply vl) (shiftSupply vr))
      (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: (UInt256.ofNat 17)
        :: (UInt256.ofNat 18) :: (UInt256.ofNat 19) :: (UInt256.ofNat 20) ::
        (UInt256.ofNat 21) :: (UInt256.ofNat 22) :: kk :: ret :: xo :: xe ::
        rest)
      = some (e :: b :: (e + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk
        + (((d ^^^ (b ||| (mLR ^^^ c))) + ((memAt (UInt256.ofNat hi)) |||
        (memAt (UInt256.ofNat lo)))) + a)))) (UInt256.ofNat vr))) ||| (mL
        &&& (UInt256.shiftRight (cM * (mLR &&& (kk + (((d ^^^ (b ||| (mLR
        ^^^ c))) + ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat
        lo)))) + a)))) (UInt256.ofNat vl))))) :: d :: (mLR &&&
        (UInt256.shiftRight (cM * (mLR &&& c)) (UInt256.ofNat 22))) :: mLR
        :: mL :: mR :: cM :: (UInt256.ofNat 17) :: (UInt256.ofNat 18) ::
        (UInt256.ofNat 19) :: (UInt256.ofNat 20) :: (UInt256.ofNat 21) ::
        (UInt256.ofNat 22) :: kk :: ret :: xo :: xe :: rest) := by
  rw [bodyEven2_cut,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt lo _),
    runOps_seg memAt seg0 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt hi _),
    runOps_seg memAt seg1 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt vl _ _ _ _ _ _ _ _ _ _ _),
    runOps_seg memAt seg2 _ _ _
      (seg2_effect memAt vl _ _ _ _ _ _ _ _ _),
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt vr _ _ _ _ _ _ _ _ _ _ _)]
  rfl

#print axioms bodyEven2_exec

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeExec
