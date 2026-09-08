import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge2

set_option warningAsError true
set_option autoImplicit false

/-!
# Group-0 even execution bridge

The concrete group-0 body is cut only at its two message offsets and two
rotation supplies.  Its arithmetic half reuses the parameterised outer rotate
proved for group 2; only the group-0 Boolean expression is class-specific.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge0

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

/-- The concrete part before the first symbolic rotation in a group-0 body. -/
def seg1Even0 : List Op :=
  [Op.mload, Op.or, Op.dup 3, Op.dup 5, Op.xor, Op.dup 10, Op.xor,
   Op.dup 5, Op.dup 11, Op.and, Op.dup 7, Op.or, Op.xor, Op.add, Op.add,
   Op.dup 16, Op.add, Op.dup 6, Op.and, Op.dup 9, Op.mul, Op.dup 1]

/-- The group-0/even body regrouped at its four symbolic opcodes. -/
theorem bodyEven0_cut (lo hi vl vr : Nat) :
    pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
        bodyEven0 (shiftSupply vl) (shiftSupply vr)
      = pushOffset lo :: (seg0 ++ (pushOffset hi :: (seg1Even0
        ++ (shiftSupply vl :: (seg2 ++ (shiftSupply vr :: seg3)))))) := rfl

/-- Parameterised unchecked execution for every group-0/even round. -/
theorem bodyEven0_exec (memAt : UInt256 → UInt256) (lo hi vl vr : Nat)
    (a b c d e mLR mL mR cM kk ret xo xe : UInt256) (rest : List UInt256) :
    runOps memAt (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload ::
      Op.or :: bodyEven0 (shiftSupply vl) (shiftSupply vr))
      (a :: b :: c :: d :: e :: mLR :: mL :: mR :: cM :: UInt256.ofNat 17 ::
        UInt256.ofNat 18 :: UInt256.ofNat 19 :: UInt256.ofNat 20 ::
        UInt256.ofNat 21 :: UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest)
      = some (e :: b :: (e + ((mR &&& UInt256.shiftRight (cM * (mLR &&& (kk
        + ((((d ||| (mR &&& c)) ^^^ (mR ^^^ (c ^^^ b))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat vr)) ||| (mL &&& UInt256.shiftRight (cM * (mLR &&& (kk
        + ((((d ||| (mR &&& c)) ^^^ (mR ^^^ (c ^^^ b))) +
        ((memAt (UInt256.ofNat hi)) ||| (memAt (UInt256.ofNat lo)))) + a))))
        (UInt256.ofNat vl)))) :: d ::
        (mLR &&& UInt256.shiftRight (cM * (mLR &&& c)) (UInt256.ofNat 22)) ::
        mLR :: mL :: mR :: cM :: UInt256.ofNat 17 :: UInt256.ofNat 18 ::
        UInt256.ofNat 19 :: UInt256.ofNat 20 :: UInt256.ofNat 21 ::
        UInt256.ofNat 22 :: kk :: ret :: xo :: xe :: rest) := by
  rw [bodyEven0_cut,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt lo _),
    runOps_seg memAt seg0 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _ (pushOffset_effect memAt hi _),
    runOps_seg memAt seg1Even0 _ _ _ rfl,
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt vl _ _ _ _ _ _ _ _ _ _ _),
    runOps_seg memAt seg2 _ _ _
      (seg2_effect memAt vl _ _ _ _ _ _ _ _ _),
    runOps_cons_effect memAt _ _ _ _
      (shiftSupply_site memAt vr _ _ _ _ _ _ _ _ _ _ _)]
  rfl

/-- The group-0 Boolean/load/constant half of slot 2. -/
theorem slot2_inner_group0 (sf : Suffix) (hstd : FrameStd sf)
    (a b c d e Xlo Xhi : UInt256) :
    sf.konst + ((((d ||| (sf.maskRv &&& c)) ^^^
        (sf.maskRv ^^^ (c ^^^ b))) + (Xhi ||| Xlo)) + a)
      = roundSum 0 { a := a, b := b, c := c, d := d, e := e }
          (Xlo ||| Xhi) sf.konst :=
  slot2_inner sf hstd a b c d e Xlo Xhi

/-- Both arithmetic halves of a group-0 result slot, at arbitrary rotations. -/
theorem slot2_group0 (sf : Suffix) (hstd : FrameStd sf)
    (a b c d e Xlo Xhi : UInt256) (sl sr : Nat) :
    e + ((sf.maskRv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& (sf.konst
              + ((((d ||| (sf.maskRv &&& c)) ^^^
                (sf.maskRv ^^^ (c ^^^ b))) + (Xhi ||| Xlo)) + a))))
            (UInt256.ofNat (32 - sr)))
        ||| (sf.maskLv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& (sf.konst
              + ((((d ||| (sf.maskRv &&& c)) ^^^
                (sf.maskRv ^^^ (c ^^^ b))) + (Xhi ||| Xlo)) + a))))
            (UInt256.ofNat (32 - sl))))
      = packedRot
          (roundSum 0 { a := a, b := b, c := c, d := d, e := e }
            (Xlo ||| Xhi) sf.konst) sl sr + e := by
  rw [slot2_inner_group0 sf hstd a b c d e Xlo Xhi]
  exact slot2_outer_group2 sf hstd _ e sl sr

/-- One parameterised group-0/even machine round is `stepFrame 0`. -/
theorem bodyEven0_stepFrame (memAt : UInt256 → UInt256)
    (lo hi sl sr : Nat) (a b c d e : UInt256) (sf : Suffix)
    (rest : List UInt256) (hstd : FrameStd sf) (hshift : SuffixStd sf) :
    let F0 : Frame := ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩
    runOps memAt
        (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
          bodyEven0 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
        (frameStack F0 ++ rest)
      = some (frameStack
          (stepFrame 0 sl sr
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
          (stepFrame 0 sl sr
            (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) F0) ++ rest =
        e :: b ::
          (packedRot
              (roundSum 0 ⟨a, b, c, d, e⟩
                (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) sf.konst)
              sl sr + e) ::
          d :: packedRol10 c :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
          sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22 ::
          sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl
  rw [hentry,
    bodyEven0_exec memAt lo hi (32 - sl) (32 - sr) a b c d e sf.maskLRv
      sf.maskLv sf.maskRv sf.cMulv sf.konst sf.ret sf.xoff sf.xend rest,
    ← hshift.h17, ← hshift.h18, ← hshift.h19, ← hshift.h20,
    ← hshift.h21, ← hshift.h22,
    hexit, slot4 sf hstd c,
    slot2_group0 sf hstd a b c d e (memAt (UInt256.ofNat lo))
      (memAt (UInt256.ofNat hi)) sl sr]

#print axioms bodyEven0_cut
#print axioms bodyEven0_exec
#print axioms slot2_inner_group0
#print axioms slot2_group0
#print axioms bodyEven0_stepFrame

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge0
