import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge2

set_option warningAsError true
set_option autoImplicit false

/-!
# Group 2, ODD phase

The odd counterpart of the even class.  Together they close the interface, and
the remaining eight classes are then mechanical.

## The odd class needs NO new Boolean-order lemma, and that is a finding

The brief anticipated "its own Boolean-order inner lemma plus phase-specific
frame packaging".  It turns out to need only the second.  Decoded from the
artifact rather than assumed:

    round 32, even   f = d ^^^ (b ||| (mLR ^^^ c))
    round 33, odd    f = e ^^^ (c ||| (mLR ^^^ b))

Those are the SAME expression.  At even phase the physical slots `a b c d e`
are the logical registers `A B C D E`; at odd phase they are `A C B E D`, so
logical `(B, C, D)` is physical `(b, c, d)` in one and `(c, b, e)` in the other.
`slot2_inner_group2` is already stated over abstract registers, so instantiating
it at the odd renaming covers this class unchanged - and so do
`slot2_outer_group2` and `slot2_group2`.

That is evidence the outer lemma is as generic as claimed, not less.  The phase
is entirely absorbed by `regsStack`, which is where it belongs.

## What is genuinely phase-specific

Only two things.  The emitted `DUP` depths differ, because the operands sit at
different stack positions - hence `segOdd0 … segOdd3` rather than reusing the
even segments.  And the frame is packed in logical order, so the odd frame is
`⟨⟨a, c, b, e, d⟩, sf, Phase.odd⟩`: `regsStack .odd` reads `[g.a, g.c, g.b,
g.e, g.d]`, which lays those out as the physical `a b c d e`.

The cut structure is identical to the even class - four symbolic sites at round
positions 0, 2, 21, 26 and stretches of 1, 18, 4 and 16 operations - so the
donor's peel shape transfers with no change.

STATUS: WRITTEN, NOT ELABORATED.  Axiom status unknown until built.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd2

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBridge
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbe
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeCut
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge2
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAssembly

/-- Odd-phase concrete stretch 0: 1 operations. -/
def segOdd0 : List Op :=
  [Op.mload]

/-- Odd-phase concrete stretch 1: 18 operations. -/
def segOdd1 : List Op :=
  [Op.mload, Op.or, Op.dup 3, Op.dup 8, Op.xor, Op.dup 5, Op.or, Op.dup 7,
   Op.xor, Op.add, Op.add, Op.dup 16, Op.add, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 1]

/-- Odd-phase concrete stretch 2: 4 operations. -/
def segOdd2 : List Op :=
  [Op.shr, Op.dup 8, Op.and, Op.swap 1]

/-- Odd-phase concrete stretch 3: 16 operations. -/
def segOdd3 : List Op :=
  [Op.shr, Op.dup 9, Op.and, Op.or, Op.dup 4, Op.add, Op.swap 1, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 15, Op.shr, Op.dup 6, Op.and, Op.swap 3]

/-- The odd round, cut at its four symbolic opcodes.  Same shape as the even
cut, right-nested so each peel takes the next symbolic opcode off the front. -/
theorem bodyOdd2_cut (lo hi sl sr : Nat) :
    pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
        bodyOdd2 (shiftSupply (32 - sl)) (shiftSupply (32 - sr))
      = pushOffset lo :: (segOdd0 ++ (pushOffset hi :: (segOdd1
        ++ (shiftSupply (32 - sl) :: (segOdd2
        ++ (shiftSupply (32 - sr) :: segOdd3)))))) := rfl

/-- **The odd-phase parametric template.**  No `simp`: four peels of a symbolic
opcode by its effect lemma, four of a concrete stretch by `rfl`. -/
theorem bodyOdd2_exec (memAt : UInt256 → UInt256) (lo hi sl sr : Nat)
    (a b c d e mLR mL mR cM kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload ::
      Op.or :: bodyOdd2 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
      (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: (UInt256.ofNat 17)
        :: (UInt256.ofNat 18) :: (UInt256.ofNat 19) :: (UInt256.ofNat 20) ::
        (UInt256.ofNat 21) :: (UInt256.ofNat 22) :: kk :: ret :: xo :: xe ::
        rest)
      = some (d :: (d + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk +
        (((e ^^^ (c ||| (mLR ^^^ b))) + ((memAt (UInt256.ofNat hi)) |||
        (memAt (UInt256.ofNat lo)))) + a)))) (UInt256.ofNat (32 - sr)))) |||
        (mL &&& (UInt256.shiftRight (cM * (mLR &&& (kk + (((e ^^^ (c |||
        (mLR ^^^ b))) + ((memAt (UInt256.ofNat hi)) ||| (memAt
        (UInt256.ofNat lo)))) + a)))) (UInt256.ofNat (32 - sl)))))) :: c ::
        (mLR &&& (UInt256.shiftRight (cM * (mLR &&& b)) (UInt256.ofNat 22)))
        :: e :: mLR :: mL :: mR :: cM :: (UInt256.ofNat 17) ::
        (UInt256.ofNat 18) :: (UInt256.ofNat 19) :: (UInt256.ofNat 20) ::
        (UInt256.ofNat 21) :: (UInt256.ofNat 22) :: kk :: ret :: xo :: xe ::
        rest) := by
  rw [bodyOdd2_cut,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt lo _),
    runOps_seg memAt segOdd0 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt hi _),
    runOps_seg memAt segOdd1 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt (32 - sl) _ _ _ _ _ _ _ _ _ _ _),
    runOps_seg memAt segOdd2 _ _ _
      (seg2_effect memAt (32 - sl) _ _ _ _ _ _ _ _ _),
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt (32 - sr) _ _ _ _ _ _ _ _ _ _ _)]
  rfl


/-- **One parameterised group-2/odd machine round is `stepFrame 2`.**

The frame is packed in LOGICAL order, so the odd frame is
`⟨⟨a, c, b, e, d⟩, sf, Phase.odd⟩`: `regsStack .odd` reads
`[g.a, g.c, g.b, g.e, g.d]`, which lays those out as the physical `a b c d e`
the machine actually has.  That renaming is the entire phase difference at the
arithmetic level - `slot2_group2` and `slot4` are reused unchanged, just
instantiated at the odd order. -/
theorem bodyOdd2_stepFrame (memAt : UInt256 → UInt256)
    (lo hi sl sr : Nat) (a b c d e : UInt256) (sf : Suffix)
    (rest : List UInt256) (hstd : FrameStd sf) (hshift : SuffixStd sf) :
    let F0 : Frame := ⟨⟨a, c, b, e, d⟩, sf, Phase.odd⟩
    runOps memAt
        (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
          bodyOdd2 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
        (frameStack F0 ++ rest)
      = some (frameStack
          (stepFrame 2 sl sr
            (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) F0)
          ++ rest) := by
  intro F0
  have hentry :
      frameStack F0 ++ rest =
        a :: b :: c :: d :: e :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
        sf.cMulv :: UInt256.ofNat 17 :: UInt256.ofNat 18 :: UInt256.ofNat 19 ::
        UInt256.ofNat 20 :: UInt256.ofNat 21 :: UInt256.ofNat 22 :: sf.konst ::
        sf.ret :: sf.xoff :: sf.xend :: rest := by
    change
      a :: b :: c :: d :: e :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
        sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22 ::
        sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest = _
    rw [hshift.h17, hshift.h18, hshift.h19, hshift.h20, hshift.h21, hshift.h22]
  have hexit :
      frameStack
          (stepFrame 2 sl sr
            (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) F0) ++ rest =
        d ::
          (packedRot
              (roundSum 2 ⟨a, c, b, e, d⟩
                (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) sf.konst)
              sl sr + d) ::
          c :: packedRol10 b :: e :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
          sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22 ::
          sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl
  rw [hentry,
    bodyOdd2_exec memAt lo hi sl sr a b c d e sf.maskLRv
      sf.maskLv sf.maskRv sf.cMulv sf.konst sf.ret sf.xoff sf.xend rest,
    ← hshift.h17, ← hshift.h18, ← hshift.h19, ← hshift.h20,
    ← hshift.h21, ← hshift.h22,
    hexit, slot4 sf hstd b,
    slot2_group2 sf hstd a c b e d (memAt (UInt256.ofNat lo))
      (memAt (UInt256.ofNat hi)) sl sr]

#print axioms bodyOdd2_cut
#print axioms bodyOdd2_exec
#print axioms bodyOdd2_stepFrame

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd2
