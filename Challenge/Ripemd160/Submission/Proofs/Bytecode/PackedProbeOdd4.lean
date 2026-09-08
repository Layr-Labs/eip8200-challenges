import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd3
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge4

set_option warningAsError true
set_option autoImplicit false

/-!
# Group 4, odd phase

The physical odd stack denotes logical registers `⟨a,c,b,e,d⟩`.  Under that
renaming, the emitted group-4 Boolean expression is exactly the already-proved
`slot2_group4`; only the concrete DUP schedule differs from the even phase.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd4

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
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge4
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd2
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAssembly

/-- Odd group-4 concrete stretch before the first symbolic rotation. -/
def segOdd1Group4 : List Op :=
  [Op.mload, Op.or, Op.dup 4, Op.dup 4, Op.xor, Op.dup 9, Op.xor, Op.dup 4,
   Op.dup 10, Op.and, Op.dup 8, Op.or, Op.xor, Op.add, Op.add, Op.dup 16,
   Op.add, Op.dup 6, Op.and, Op.dup 9, Op.mul, Op.dup 1]

/-- The odd group-4 body cut at its four symbolic sites. -/
theorem bodyOdd4_cut (lo hi sl sr : Nat) :
    pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
        bodyOdd4 (shiftSupply (32 - sl)) (shiftSupply (32 - sr))
      = pushOffset lo :: (segOdd0 ++ (pushOffset hi :: (segOdd1Group4
        ++ (shiftSupply (32 - sl) :: (segOdd2
        ++ (shiftSupply (32 - sr) :: segOdd3)))))) := rfl

/-- Parameterised unchecked execution for every group-4/odd round. -/
theorem bodyOdd4_exec (memAt : UInt256 → UInt256) (lo hi sl sr : Nat)
    (a b c d e mLR mL mR cM kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload ::
      Op.or :: bodyOdd4 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
      (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: UInt256.ofNat 17 ::
        UInt256.ofNat 18 :: UInt256.ofNat 19 :: UInt256.ofNat 20 ::
        UInt256.ofNat 21 :: UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest)
      = some (d :: (d + ((mR &&& UInt256.shiftRight (cM * (mLR &&& (kk +
        ((((e ||| (mL &&& b)) ^^^ (mL ^^^ (b ^^^ c))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat (32 - sr))) ||| (mL &&& UInt256.shiftRight
        (cM * (mLR &&& (kk + ((((e ||| (mL &&& b)) ^^^
          (mL ^^^ (b ^^^ c))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat (32 - sl))))) :: c ::
        (mLR &&& UInt256.shiftRight (cM * (mLR &&& b)) (UInt256.ofNat 22)) ::
        e :: mLR :: mL :: mR :: cM :: UInt256.ofNat 17 :: UInt256.ofNat 18 ::
        UInt256.ofNat 19 :: UInt256.ofNat 20 :: UInt256.ofNat 21 ::
        UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest) := by
  rw [bodyOdd4_cut,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt lo _),
    runOps_seg memAt segOdd0 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt hi _),
    runOps_seg memAt segOdd1Group4 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt (32 - sl) _ _ _ _ _ _ _ _ _ _ _),
    runOps_seg memAt segOdd2 _ _ _
      (seg2_effect memAt (32 - sl) _ _ _ _ _ _ _ _ _),
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt (32 - sr) _ _ _ _ _ _ _ _ _ _ _)]
  rfl

/-- One parameterised group-4/odd machine round is `stepFrame 4`. -/
theorem bodyOdd4_stepFrame (memAt : UInt256 → UInt256)
    (lo hi sl sr : Nat) (a b c d e : UInt256) (sf : Suffix)
    (rest : List UInt256) (hstd : FrameStd sf) (hshift : SuffixStd sf) :
    let F0 : Frame := ⟨⟨a, c, b, e, d⟩, sf, Phase.odd⟩
    runOps memAt
        (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
          bodyOdd4 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
        (frameStack F0 ++ rest)
      = some (frameStack
          (stepFrame 4 sl sr
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
          (stepFrame 4 sl sr
            (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) F0) ++ rest =
        d ::
          (packedRot
              (roundSum 4 ⟨a, c, b, e, d⟩
                (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) sf.konst)
              sl sr + d) ::
          c :: packedRol10 b :: e :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
          sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22 ::
          sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl
  rw [hentry,
    bodyOdd4_exec memAt lo hi sl sr a b c d e sf.maskLRv
      sf.maskLv sf.maskRv sf.cMulv sf.konst sf.ret sf.xoff sf.xend rest,
    ← hshift.h17, ← hshift.h18, ← hshift.h19, ← hshift.h20,
    ← hshift.h21, ← hshift.h22,
    hexit, slot4 sf hstd b,
    slot2_group4 sf hstd a c b e d (memAt (UInt256.ofNat lo))
      (memAt (UInt256.ofNat hi)) sl sr]

#print axioms bodyOdd4_cut
#print axioms bodyOdd4_exec
#print axioms bodyOdd4_stepFrame

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd4
