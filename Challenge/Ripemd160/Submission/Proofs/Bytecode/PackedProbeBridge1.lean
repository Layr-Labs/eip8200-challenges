import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge0

set_option warningAsError true
set_option autoImplicit false

/-!
# Group-1 even execution bridge

The emitted Boolean term is checked against `bodyEven1`: this is the select
shape with `(p,q,r) = (b,c,d)` and mask `maskR`.  The message and rotation
sites remain symbolic, so one theorem covers every even round in group 1.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge1

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepOrder
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBridge
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAssembly
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbe
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeCut
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge2

/-- The concrete part before the first symbolic rotation in a group-1 body. -/
def seg1Even1 : List Op :=
  [Op.mload, Op.or, Op.dup 4, Op.dup 6, Op.xor, Op.dup 4, Op.and, Op.dup 6,
   Op.xor, Op.dup 4, Op.dup 6, Op.and, Op.dup 6, Op.dup 8, Op.or, Op.xor,
   Op.dup 11, Op.and, Op.xor, Op.add, Op.add, Op.dup 16, Op.add, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 1]

/-- The group-1/even body regrouped at its four symbolic opcodes. -/
theorem bodyEven1_cut (lo hi vl vr : Nat) :
    pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
        bodyEven1 (shiftSupply vl) (shiftSupply vr)
      = pushOffset lo :: (seg0 ++ (pushOffset hi :: (seg1Even1
        ++ (shiftSupply vl :: (seg2 ++ (shiftSupply vr :: seg3)))))) := rfl

/-- Parameterised unchecked execution for every group-1/even round. -/
theorem bodyEven1_exec (memAt : UInt256 → UInt256) (lo hi vl vr : Nat)
    (a b c d e mLR mL mR cM kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload ::
      Op.or :: bodyEven1 (shiftSupply vl) (shiftSupply vr))
      (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: UInt256.ofNat 17 ::
        UInt256.ofNat 18 :: UInt256.ofNat 19 :: UInt256.ofNat 20 ::
        UInt256.ofNat 21 :: UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest)
      = some (e :: b :: (e + ((mR &&& UInt256.shiftRight (cM * (mLR &&& (kk
        + ((((mR &&& ((d ||| c) ^^^ (c &&& b))) ^^^
          (d ^^^ (b &&& (d ^^^ c)))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat vr)) ||| (mL &&& UInt256.shiftRight (cM * (mLR &&& (kk
        + ((((mR &&& ((d ||| c) ^^^ (c &&& b))) ^^^
          (d ^^^ (b &&& (d ^^^ c)))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat vl)))) :: d ::
        (mLR &&& UInt256.shiftRight (cM * (mLR &&& c)) (UInt256.ofNat 22)) ::
        mLR :: mL :: mR :: cM :: UInt256.ofNat 17 :: UInt256.ofNat 18 ::
        UInt256.ofNat 19 :: UInt256.ofNat 20 :: UInt256.ofNat 21 ::
        UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest) := by
  rw [bodyEven1_cut,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt lo _),
    runOps_seg memAt seg0 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt hi _),
    runOps_seg memAt seg1Even1 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt vl _ _ _ _ _ _ _ _ _ _ _),
    runOps_seg memAt seg2 _ _ _
      (seg2_effect memAt vl _ _ _ _ _ _ _ _ _),
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt vr _ _ _ _ _ _ _ _ _ _ _)]
  rfl

/-- The group-1 select/load/constant half of slot 2. -/
theorem slot2_inner_group1 (sf : Suffix) (hstd : FrameStd sf)
    (a b c d e Xlo Xhi : UInt256) :
    sf.konst + ((((sf.maskRv &&& ((d ||| c) ^^^ (c &&& b))) ^^^
        (d ^^^ (b &&& (d ^^^ c)))) + (Xhi ||| Xlo)) + a)
      = roundSum 1 { a := a, b := b, c := c, d := d, e := e }
          (Xlo ||| Xhi) sf.konst := by
  unfold roundSum
  rw [hstd.mR, load_order Xlo Xhi,
    fSelect_order b c d b c d maskR]
  exact sum_order _ _

/-- Both arithmetic halves of a group-1 result slot, at arbitrary rotations. -/
theorem slot2_group1 (sf : Suffix) (hstd : FrameStd sf)
    (a b c d e Xlo Xhi : UInt256) (sl sr : Nat) :
    e + ((sf.maskRv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& (sf.konst
              + ((((sf.maskRv &&& ((d ||| c) ^^^ (c &&& b))) ^^^
                (d ^^^ (b &&& (d ^^^ c)))) + (Xhi ||| Xlo)) + a))))
            (UInt256.ofNat (32 - sr)))
        ||| (sf.maskLv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& (sf.konst
              + ((((sf.maskRv &&& ((d ||| c) ^^^ (c &&& b))) ^^^
                (d ^^^ (b &&& (d ^^^ c)))) + (Xhi ||| Xlo)) + a))))
            (UInt256.ofNat (32 - sl))))
      = packedRot
          (roundSum 1 { a := a, b := b, c := c, d := d, e := e }
            (Xlo ||| Xhi) sf.konst) sl sr + e := by
  rw [slot2_inner_group1 sf hstd a b c d e Xlo Xhi]
  exact slot2_outer_group2 sf hstd _ e sl sr

/-- One parameterised group-1/even machine round is `stepFrame 1`. -/
theorem bodyEven1_stepFrame (memAt : UInt256 → UInt256)
    (lo hi sl sr : Nat) (a b c d e : UInt256) (sf : Suffix)
    (rest : List UInt256) (hstd : FrameStd sf) (hshift : SuffixStd sf) :
    let F0 : Frame := ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩
    runOps memAt
        (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
          bodyEven1 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
        (frameStack F0 ++ rest)
      = some (frameStack
          (stepFrame 1 sl sr
            (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) F0) ++ rest) := by
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
        e :: b ::
          (packedRot
              (roundSum 1 ⟨a, b, c, d, e⟩
                (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) sf.konst)
              sl sr + e) ::
          d :: packedRol10 c :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
          sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22 ::
          sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl
  rw [hentry,
    bodyEven1_exec memAt lo hi (32 - sl) (32 - sr) a b c d e sf.maskLRv
      sf.maskLv sf.maskRv sf.cMulv sf.konst sf.ret sf.xoff sf.xend rest,
    ← hshift.h17, ← hshift.h18, ← hshift.h19, ← hshift.h20,
    ← hshift.h21, ← hshift.h22,
    hexit, slot4 sf hstd c,
    slot2_group1 sf hstd a b c d e (memAt (UInt256.ofNat lo))
      (memAt (UInt256.ofNat hi)) sl sr]

#print axioms bodyEven1_cut
#print axioms bodyEven1_exec
#print axioms slot2_inner_group1
#print axioms slot2_group1
#print axioms bodyEven1_stepFrame

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge1
