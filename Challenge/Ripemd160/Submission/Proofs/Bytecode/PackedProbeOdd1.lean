import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge1

set_option warningAsError true
set_option autoImplicit false

/-!
# Group 1, odd phase

The physical odd stack denotes logical registers `⟨a,c,b,e,d⟩`.  Under that
renaming the emitted select expression is exactly the proved group-1 bridge.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd1

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
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge1
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd2
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAssembly

/-- Odd group-1 concrete stretch before the first symbolic rotation. -/
def segOdd1Group1 : List Op :=
  [Op.mload, Op.or, Op.dup 3, Op.dup 7, Op.xor, Op.dup 5, Op.and, Op.dup 7,
   Op.xor, Op.dup 5, Op.dup 5, Op.and, Op.dup 5, Op.dup 9, Op.or, Op.xor,
   Op.dup 11, Op.and, Op.xor, Op.add, Op.add, Op.dup 16, Op.add, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 1]

/-- The odd group-1 body cut at its four symbolic sites. -/
theorem bodyOdd1_cut (lo hi sl sr : Nat) :
    pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
        bodyOdd1 (shiftSupply (32 - sl)) (shiftSupply (32 - sr))
      = pushOffset lo :: (segOdd0 ++ (pushOffset hi :: (segOdd1Group1
        ++ (shiftSupply (32 - sl) :: (segOdd2
        ++ (shiftSupply (32 - sr) :: segOdd3)))))) := rfl

/-- Parameterised unchecked execution for every group-1/odd round. -/
theorem bodyOdd1_exec (memAt : UInt256 → UInt256) (lo hi sl sr : Nat)
    (a b c d e mLR mL mR cM kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload ::
      Op.or :: bodyOdd1 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
      (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: UInt256.ofNat 17 ::
        UInt256.ofNat 18 :: UInt256.ofNat 19 :: UInt256.ofNat 20 ::
        UInt256.ofNat 21 :: UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest)
      = some (d :: (d + ((mR &&& UInt256.shiftRight (cM * (mLR &&& (kk +
        ((((mR &&& ((e ||| b) ^^^ (b &&& c))) ^^^
          (e ^^^ (c &&& (e ^^^ b)))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat (32 - sr))) ||| (mL &&& UInt256.shiftRight
        (cM * (mLR &&& (kk + ((((mR &&& ((e ||| b) ^^^ (b &&& c))) ^^^
          (e ^^^ (c &&& (e ^^^ b)))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat (32 - sl))))) :: c ::
        (mLR &&& UInt256.shiftRight (cM * (mLR &&& b)) (UInt256.ofNat 22)) ::
        e :: mLR :: mL :: mR :: cM :: UInt256.ofNat 17 :: UInt256.ofNat 18 ::
        UInt256.ofNat 19 :: UInt256.ofNat 20 :: UInt256.ofNat 21 ::
        UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest) := by
  rw [bodyOdd1_cut,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt lo _),
    runOps_seg memAt segOdd0 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt hi _),
    runOps_seg memAt segOdd1Group1 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt (32 - sl) _ _ _ _ _ _ _ _ _ _ _),
    runOps_seg memAt segOdd2 _ _ _
      (seg2_effect memAt (32 - sl) _ _ _ _ _ _ _ _ _),
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt (32 - sr) _ _ _ _ _ _ _ _ _ _ _)]
  rfl

/-- One parameterised group-1/odd machine round is `stepFrame 1`. -/
theorem bodyOdd1_stepFrame (memAt : UInt256 → UInt256)
    (lo hi sl sr : Nat) (a b c d e : UInt256) (sf : Suffix)
    (rest : List UInt256) (hstd : FrameStd sf) (hshift : SuffixStd sf) :
    let F0 : Frame := ⟨⟨a, c, b, e, d⟩, sf, Phase.odd⟩
    runOps memAt
        (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
          bodyOdd1 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
        (frameStack F0 ++ rest)
      = some (frameStack
          (stepFrame 1 sl sr
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
          (stepFrame 1 sl sr
            (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) F0) ++ rest =
        d ::
          (packedRot
              (roundSum 1 ⟨a, c, b, e, d⟩
                (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) sf.konst)
              sl sr + d) ::
          c :: packedRol10 b :: e :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
          sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22 ::
          sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl
  rw [hentry,
    bodyOdd1_exec memAt lo hi sl sr a b c d e sf.maskLRv
      sf.maskLv sf.maskRv sf.cMulv sf.konst sf.ret sf.xoff sf.xend rest,
    ← hshift.h17, ← hshift.h18, ← hshift.h19, ← hshift.h20,
    ← hshift.h21, ← hshift.h22,
    hexit, slot4 sf hstd b,
    slot2_group1 sf hstd a c b e d (memAt (UInt256.ofNat lo))
      (memAt (UInt256.ofNat hi)) sl sr]

#print axioms bodyOdd1_cut
#print axioms bodyOdd1_exec
#print axioms bodyOdd1_stepFrame

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd1
