import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge3

set_option warningAsError true
set_option autoImplicit false

/-!
# Group-4 even execution bridge

Group 4 has the group-0 Boolean shape with the opposite lane mask.  The
emitted term is therefore normalized with `f4_order` and `maskL`; message
offsets and rotations remain symbolic.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge4

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

/-- The concrete part before the first symbolic rotation in a group-4 body. -/
def seg1Even4 : List Op :=
  [Op.mload, Op.or, Op.dup 3, Op.dup 5, Op.xor, Op.dup 9, Op.xor,
   Op.dup 5, Op.dup 10, Op.and, Op.dup 7, Op.or, Op.xor, Op.add, Op.add,
   Op.dup 16, Op.add, Op.dup 6, Op.and, Op.dup 9, Op.mul, Op.dup 1]

/-- The group-4/even body regrouped at its four symbolic opcodes. -/
theorem bodyEven4_cut (lo hi vl vr : Nat) :
    pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
        bodyEven4 (shiftSupply vl) (shiftSupply vr)
      = pushOffset lo :: (seg0 ++ (pushOffset hi :: (seg1Even4
        ++ (shiftSupply vl :: (seg2 ++ (shiftSupply vr :: seg3)))))) := rfl

/-- Parameterised unchecked execution for every group-4/even round. -/
theorem bodyEven4_exec (memAt : UInt256 → UInt256) (lo hi vl vr : Nat)
    (a b c d e mLR mL mR cM kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload ::
      Op.or :: bodyEven4 (shiftSupply vl) (shiftSupply vr))
      (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: UInt256.ofNat 17 ::
        UInt256.ofNat 18 :: UInt256.ofNat 19 :: UInt256.ofNat 20 ::
        UInt256.ofNat 21 :: UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest)
      = some (e :: b :: (e + ((mR &&& UInt256.shiftRight (cM * (mLR &&& (kk
        + ((((d ||| (mL &&& c)) ^^^ (mL ^^^ (c ^^^ b))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat vr)) ||| (mL &&& UInt256.shiftRight (cM * (mLR &&& (kk
        + ((((d ||| (mL &&& c)) ^^^ (mL ^^^ (c ^^^ b))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat vl)))) :: d ::
        (mLR &&& UInt256.shiftRight (cM * (mLR &&& c)) (UInt256.ofNat 22)) ::
        mLR :: mL :: mR :: cM :: UInt256.ofNat 17 :: UInt256.ofNat 18 ::
        UInt256.ofNat 19 :: UInt256.ofNat 20 :: UInt256.ofNat 21 ::
        UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest) := by
  rw [bodyEven4_cut,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt lo _),
    runOps_seg memAt seg0 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt hi _),
    runOps_seg memAt seg1Even4 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt vl _ _ _ _ _ _ _ _ _ _ _),
    runOps_seg memAt seg2 _ _ _
      (seg2_effect memAt vl _ _ _ _ _ _ _ _ _),
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt vr _ _ _ _ _ _ _ _ _ _ _)]
  rfl

/-- The group-4 Boolean/load/constant half of slot 2. -/
theorem slot2_inner_group4 (sf : Suffix) (hstd : FrameStd sf)
    (a b c d e Xlo Xhi : UInt256) :
    sf.konst + ((((d ||| (sf.maskLv &&& c)) ^^^
        (sf.maskLv ^^^ (c ^^^ b))) + (Xhi ||| Xlo)) + a)
      = roundSum 4 { a := a, b := b, c := c, d := d, e := e }
          (Xlo ||| Xhi) sf.konst := by
  unfold roundSum
  rw [hstd.mL, load_order Xlo Xhi, f4_order b c d maskL]
  exact sum_order _ _

/-- Both arithmetic halves of a group-4 result slot, at arbitrary rotations. -/
theorem slot2_group4 (sf : Suffix) (hstd : FrameStd sf)
    (a b c d e Xlo Xhi : UInt256) (sl sr : Nat) :
    e + ((sf.maskRv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& (sf.konst
              + ((((d ||| (sf.maskLv &&& c)) ^^^
                (sf.maskLv ^^^ (c ^^^ b))) + (Xhi ||| Xlo)) + a))))
            (UInt256.ofNat (32 - sr)))
        ||| (sf.maskLv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& (sf.konst
              + ((((d ||| (sf.maskLv &&& c)) ^^^
                (sf.maskLv ^^^ (c ^^^ b))) + (Xhi ||| Xlo)) + a))))
            (UInt256.ofNat (32 - sl))))
      = packedRot
          (roundSum 4 { a := a, b := b, c := c, d := d, e := e }
            (Xlo ||| Xhi) sf.konst) sl sr + e := by
  rw [slot2_inner_group4 sf hstd a b c d e Xlo Xhi]
  exact slot2_outer_group2 sf hstd _ e sl sr

/-- One parameterised group-4/even machine round is `stepFrame 4`. -/
theorem bodyEven4_stepFrame (memAt : UInt256 → UInt256)
    (lo hi sl sr : Nat) (a b c d e : UInt256) (sf : Suffix)
    (rest : List UInt256) (hstd : FrameStd sf) (hshift : SuffixStd sf) :
    let F0 : Frame := ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩
    runOps memAt
        (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
          bodyEven4 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
        (frameStack F0 ++ rest)
      = some (frameStack
          (stepFrame 4 sl sr
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
          (stepFrame 4 sl sr
            (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) F0) ++ rest =
        e :: b ::
          (packedRot
              (roundSum 4 ⟨a, b, c, d, e⟩
                (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) sf.konst)
              sl sr + e) ::
          d :: packedRol10 c :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
          sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22 ::
          sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl
  rw [hentry,
    bodyEven4_exec memAt lo hi (32 - sl) (32 - sr) a b c d e sf.maskLRv
      sf.maskLv sf.maskRv sf.cMulv sf.konst sf.ret sf.xoff sf.xend rest,
    ← hshift.h17, ← hshift.h18, ← hshift.h19, ← hshift.h20,
    ← hshift.h21, ← hshift.h22,
    hexit, slot4 sf hstd c,
    slot2_group4 sf hstd a b c d e (memAt (UInt256.ofNat lo))
      (memAt (UInt256.ofNat hi)) sl sr]

#print axioms bodyEven4_cut
#print axioms bodyEven4_exec
#print axioms slot2_inner_group4
#print axioms slot2_group4
#print axioms bodyEven4_stepFrame

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge4
