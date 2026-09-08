import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeExec

set_option warningAsError true
set_option autoImplicit false

/-!
# Group-2 even execution bridge

`bodyEven2_exec` is the parameterised unchecked execution certificate.  This
module changes only its two computed stack slots into the arithmetic model and
then packages the result as `stepFrame`.  The rotation arguments stay symbolic:
the emitted shifts are `32 - sl` and `32 - sr`, exactly as in `packedRot`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge2

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
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeExec

/-- The short group-2 Boolean expression, reversed message load, and cached
constant order are exactly `roundSum 2`. -/
theorem slot2_inner_group2 (sf : Suffix) (hstd : FrameStd sf)
    (a b c d e Xlo Xhi : UInt256) :
    sf.konst + (((d ^^^ (b ||| (sf.maskLRv ^^^ c))) + (Xhi ||| Xlo)) + a)
      = roundSum 2 { a := a, b := b, c := c, d := d, e := e }
          (Xlo ||| Xhi) sf.konst := by
  unfold roundSum
  rw [hstd.mLR, load_order Xlo Xhi, fShort_order b c d maskLR]
  exact sum_order _ _

/-- The emitted high-first rotate and write-back are `packedRot`, for arbitrary
rotation amounts.  Keeping `32 - sl` and `32 - sr` symbolic avoids every
literal-only `11/8` assumption from the round-0 bridge. -/
theorem slot2_outer_group2 (sf : Suffix) (hstd : FrameStd sf)
    (S e : UInt256) (sl sr : Nat) :
    e + ((sf.maskRv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& S)) (UInt256.ofNat (32 - sr)))
        ||| (sf.maskLv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& S)) (UInt256.ofNat (32 - sl))))
      = packedRot S sl sr + e := by
  rw [hstd.mR, hstd.mL, hstd.mLR, hstd.cM]
  have hpr : packedRot S sl sr
      = (UInt256.shiftRight (cMul * (S &&& maskLR))
            (UInt256.ofNat (32 - sl)) &&& maskL)
        ||| (UInt256.shiftRight (cMul * (S &&& maskLR))
            (UInt256.ofNat (32 - sr)) &&& maskR) := rfl
  rw [hpr, uand_comm maskLR S]
  rw [rot_order
      (UInt256.shiftRight (cMul * (S &&& maskLR))
        (UInt256.ofNat (32 - sl)))
      (UInt256.shiftRight (cMul * (S &&& maskLR))
        (UInt256.ofNat (32 - sr))) maskL maskR]
  exact writeback_order e _

/-- Both arithmetic halves of the group-2 result slot. -/
theorem slot2_group2 (sf : Suffix) (hstd : FrameStd sf)
    (a b c d e Xlo Xhi : UInt256) (sl sr : Nat) :
    e + ((sf.maskRv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& (sf.konst
              + (((d ^^^ (b ||| (sf.maskLRv ^^^ c))) + (Xhi ||| Xlo)) + a))))
            (UInt256.ofNat (32 - sr)))
        ||| (sf.maskLv &&& UInt256.shiftRight
            (sf.cMulv * (sf.maskLRv &&& (sf.konst
              + (((d ^^^ (b ||| (sf.maskLRv ^^^ c))) + (Xhi ||| Xlo)) + a))))
            (UInt256.ofNat (32 - sl))))
      = packedRot
          (roundSum 2 { a := a, b := b, c := c, d := d, e := e }
            (Xlo ||| Xhi) sf.konst) sl sr + e := by
  rw [slot2_inner_group2 sf hstd a b c d e Xlo Xhi]
  exact slot2_outer_group2 sf hstd _ e sl sr

/-- One parameterised group-2/even machine round is `stepFrame 2`. -/
theorem bodyEven2_stepFrame (memAt : UInt256 → UInt256)
    (lo hi sl sr : Nat) (a b c d e : UInt256) (sf : Suffix)
    (rest : List UInt256) (hstd : FrameStd sf) (hshift : SuffixStd sf) :
    let F0 : Frame := ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩
    runOps memAt
        (pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
          bodyEven2 (shiftSupply (32 - sl)) (shiftSupply (32 - sr)))
        (frameStack F0 ++ rest)
      = some (frameStack
          (stepFrame 2 sl sr
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
          (stepFrame 2 sl sr
            (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) F0) ++ rest =
        e :: b ::
          (packedRot
              (roundSum 2 ⟨a, b, c, d, e⟩
                (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi)) sf.konst)
              sl sr + e) ::
          d :: packedRol10 c :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
          sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22 ::
          sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl
  rw [hentry,
    bodyEven2_exec memAt lo hi (32 - sl) (32 - sr) a b c d e sf.maskLRv
      sf.maskLv sf.maskRv sf.cMulv sf.konst sf.ret sf.xoff sf.xend rest,
    ← hshift.h17, ← hshift.h18, ← hshift.h19, ← hshift.h20,
    ← hshift.h21, ← hshift.h22,
    hexit, slot4 sf hstd c,
    slot2_group2 sf hstd a b c d e (memAt (UInt256.ofNat lo))
      (memAt (UInt256.ofNat hi)) sl sr]

#print axioms slot2_inner_group2
#print axioms slot2_outer_group2
#print axioms slot2_group2
#print axioms bodyEven2_stepFrame

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge2
