import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAssembly
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0Template

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Round 0, end to end

`step0_template` says what the machine leaves.  `slot2` and `slot4` say the two
live values are the arithmetic layer's.  This is the congruence joining them, so
that one round of the real bytecode IS one `stepFrame`.

The proof is four rewrites and no reasoning: normalise the entry stack to the
cons form the template is stated over, apply the template, normalise the target
to its cons form, then rewrite the two live slots.  Everything else on the two
lists is already syntactically identical - the three register moves, the
fourteen suffix slots, and the tail.

Both stack normalisations are `rfl`: `frameStack` is `regsStack ++ suffixStack`,
and with the phase a literal both reduce to cons cells.  Using `rfl` rather than
`simp [frameStack, ...]` keeps this immune to the head-versus-notation problem
that cost a rebuild in `slot2_outer`.

STATUS: WRITTEN, NOT ELABORATED.  Axiom status unknown until built.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRound0

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0Template
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBridge
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAssembly

/-- **One round of the real bytecode is one `stepFrame`.**  Round 0 of `ed34`,
over an arbitrary tail and arbitrary register and suffix contents, given only
that the suffix holds the constants the arithmetic layer names. -/
theorem step0_round (memAt : UInt256 → UInt256)
    (a b c d e : UInt256) (sf : Suffix) (rest : List UInt256)
    (hstd : FrameStd sf) :
    let F0 : Frame := ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩
    runOps memAt step0Ops (frameStack F0 ++ rest)
      = some (frameStack (stepFrame 0 11 8 (memAt 0 ||| memAt (UInt256.ofNat 88)) F0) ++ rest) := by
  intro F0
  have hentry :
      frameStack F0 ++ rest =
        a :: b :: c :: d :: e :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
        sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22
        :: sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl
  have hexit :
      frameStack (stepFrame 0 11 8 (memAt 0 ||| memAt (UInt256.ofNat 88)) F0) ++ rest =
        e :: b :: (packedRot (roundSum 0 ⟨a, b, c, d, e⟩ (memAt 0 ||| memAt (UInt256.ofNat 88)) sf.konst) 11 8 + e)
        :: d :: (packedRol10 c) :: sf.maskLRv :: sf.maskLv :: sf.maskRv ::
        sf.cMulv :: sf.s17 :: sf.s18 :: sf.s19 :: sf.s20 :: sf.s21 :: sf.s22
        :: sf.konst :: sf.ret :: sf.xoff :: sf.xend :: rest := rfl
  rw [hentry, step0_template memAt a b c d e sf.maskLRv sf.maskLv sf.maskRv
    sf.cMulv sf.s17 sf.s18 sf.s19 sf.s20 sf.s21 sf.s22 sf.konst sf.ret
    sf.xoff sf.xend rest, hexit, slot4 sf hstd c, slot2 sf hstd a b c d e (memAt 0) (memAt (UInt256.ofNat 88))]

#print axioms step0_round

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRound0
