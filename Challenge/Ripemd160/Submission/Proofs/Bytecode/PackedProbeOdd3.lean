import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge3

set_option warningAsError true
set_option autoImplicit false

/-!
# Group 3, odd phase

Under odd register order `⟨a,c,b,e,d⟩`, group 3 instantiates the select base
as `(p,q,r) = (e,c,b)` while retaining correction inputs `(c,b,e)`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd3

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
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge3
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd2
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAssembly

/-- Odd group-3 concrete stretch before the first symbolic rotation. -/
def segOdd1Group3 : List Op :=
  [Op.mload, Op.or, Op.dup 4, Op.dup 4, Op.xor, Op.dup 7, Op.and, Op.dup 4,
   Op.xor, Op.dup 5, Op.dup 5, Op.and, Op.dup 5, Op.dup 9, Op.or, Op.xor,
   Op.dup 11, Op.and, Op.xor, Op.add, Op.add, Op.dup 16, Op.add, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 1]

/-- The odd group-3 body cut at its four symbolic sites. -/
theorem bodyOdd3_cut (lo hi sl sr : Nat) :
    pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
        bodyOdd3 (shiftSupply (32 - sl)) (shiftSupply (32 - sr))
      = pushOffset lo :: (segOdd0 ++ (pushOffset hi :: (segOdd1Group3
        ++ (shiftSupply (32 - sl) :: (segOdd2
        ++ (shiftSupply (32 - sr) :: segOdd3)))))) := rfl

/-- Parameterised unchecked execution for every group-3/odd round. -/
theorem bodyOdd3_exec (memAt : UInt256 → UInt256) (lo hi sl sr : Nat)
    (a b c d e mLR mL mR cM kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload ::
      Op.or :: bodyOdd3 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
      (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: UInt256.ofNat 17 ::
        UInt256.ofNat 18 :: UInt256.ofNat 19 :: UInt256.ofNat 20 ::
        UInt256.ofNat 21 :: UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest)
      = some (d :: (d + ((mR &&& UInt256.shiftRight (cM * (mLR &&& (kk +
        ((((mR &&& ((e ||| b) ^^^ (b &&& c))) ^^^
          (b ^^^ (e &&& (b ^^^ c)))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat (32 - sr))) ||| (mL &&& UInt256.shiftRight
        (cM * (mLR &&& (kk + ((((mR &&& ((e ||| b) ^^^ (b &&& c))) ^^^
          (b ^^^ (e &&& (b ^^^ c)))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat (32 - sl))))) :: c ::
        (mLR &&& UInt256.shiftRight (cM * (mLR &&& b)) (UInt256.ofNat 22)) ::
        e :: mLR :: mL :: mR :: cM :: UInt256.ofNat 17 :: UInt256.ofNat 18 ::
        UInt256.ofNat 19 :: UInt256.ofNat 20 :: UInt256.ofNat 21 ::
        UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest) := by
  rw [bodyOdd3_cut,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt lo _),
    runOps_seg memAt segOdd0 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt hi _),
    runOps_seg memAt segOdd1Group3 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt (32 - sl) _ _ _ _ _ _ _ _ _ _ _),
    runOps_seg memAt segOdd2 _ _ _
      (seg2_effect memAt (32 - sl) _ _ _ _ _ _ _ _ _),
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt (32 - sr) _ _ _ _ _ _ _ _ _ _ _)]
  rfl

/-- One parameterised group-3/odd machine round is `stepFrame 3`. -/
theorem bodyOdd3_stepFrame (memAt : UInt256 → UInt256)
    (lo hi sl sr : Nat) (a b c d e : UInt256) (sf : Suffix)
    (rest : List UInt256) (hstd : FrameStd sf) (hshift : SuffixStd sf) :
    let F0 : Frame := ⟨⟨a, c, b, e, d⟩, sf, Phase.odd⟩
    runOps memAt
        (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
          bodyOdd3 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
        (frameStack F0 ++ rest)
      = some (frameStack
          (stepFrame 3 sl sr
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
          (stepFrame 3 sl sr
            (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) F0) ++ rest =
        d ::
          (packedRot
              (roundSum 3 ⟨a, c, b, e, d⟩
                (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) sf.konst)
              sl sr + d) ::
          c :: packedRol10 b :: e :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
          sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22 ::
          sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl
  rw [hentry,
    bodyOdd3_exec memAt lo hi sl sr a b c d e sf.maskLRv
      sf.maskLv sf.maskRv sf.cMulv sf.konst sf.ret sf.xoff sf.xend rest,
    ← hshift.h17, ← hshift.h18, ← hshift.h19, ← hshift.h20,
    ← hshift.h21, ← hshift.h22,
    hexit, slot4 sf hstd b,
    slot2_group3 sf hstd a c b e d (memAt (UInt256.ofNat lo))
      (memAt (UInt256.ofNat hi)) sl sr]

#print axioms bodyOdd3_cut
#print axioms bodyOdd3_exec
#print axioms bodyOdd3_stepFrame

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd3
