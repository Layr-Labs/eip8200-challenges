import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd4

set_option warningAsError true
set_option autoImplicit false

/-!
# Uniform execution certificate for every emitted packed round

The ten phase/group-specific certificates are assembled here at the actual
`emitRound` boundary.  This module is deliberately independent of the located
gas bridge: it states only the abstract `runOps` fact needed by the round
sequence induction.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAllRoundExec

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBridge

/-- The parameterised opcode family represented by the ten class lemmas. -/
def roundOps (p : Phase) (group lo hi sl sr : Nat) : List Op :=
  pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
    (match p, group with
    | .even, 0 => bodyEven0
    | .odd, 0 => bodyOdd0
    | .even, 1 => bodyEven1
    | .odd, 1 => bodyOdd1
    | .even, 2 => bodyEven2
    | .odd, 2 => bodyOdd2
    | .even, 3 => bodyEven3
    | .odd, 3 => bodyOdd3
    | .even, _ => bodyEven4
    | .odd, _ => bodyOdd4) (shiftSupply (32 - sl)) (shiftSupply (32 - sr))

/-- The parameterised family is definitionally the real table-driven emitter. -/
theorem roundOps_emitRound (p : Phase) (i : Nat) :
    roundOps p (i / 16) (16 * Crypto.Ripemd160.r[i]!)
      (16 * Crypto.Ripemd160.rP[i]! + 8)
      Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
      = emitRound p i := by
  unfold roundOps emitRound loadPrefix roundBody
  cases p <;> generalize i / 16 = g <;>
    rcases g with _ | (_ | (_ | (_ | g))) <;> rfl

/-- Every table-emitted round executes as its abstract `stepFrame`, for either
physical phase and every one of the five RIPEMD Boolean groups. -/
theorem emitted_round_exec (i : Nat) (hi : i < 80)
    (memAt : UInt256 → UInt256) (f : Frame) (rest : List UInt256)
    (hstd : FrameStd f.suf) (hshift : SuffixStd f.suf) :
    runOps memAt (emitRound f.phase i) (frameStack f ++ rest)
      = some (frameStack
          (stepFrame (i / 16) Crypto.Ripemd160.s[i]!
            Crypto.Ripemd160.sP[i]!
            (memAt (UInt256.ofNat (16 * Crypto.Ripemd160.r[i]!)) |||
              memAt (UInt256.ofNat (16 * Crypto.Ripemd160.rP[i]! + 8))) f)
          ++ rest) := by
  rw [← roundOps_emitRound]
  obtain ⟨⟨a, b, c, d, e⟩, sf, phase⟩ := f
  have hgroups : i / 16 = 0 ∨ i / 16 = 1 ∨ i / 16 = 2 ∨
      i / 16 = 3 ∨ i / 16 = 4 := by omega
  rcases hgroups with h | h | h | h | h
  · cases phase
    · simpa only [roundOps, h] using
        PackedProbeBridge0.bodyEven0_stepFrame memAt
          (16 * Crypto.Ripemd160.r[i]!) (16 * Crypto.Ripemd160.rP[i]! + 8)
          Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          a b c d e sf rest hstd hshift
    · simpa only [roundOps, h] using
        PackedProbeOdd0.bodyOdd0_stepFrame memAt
          (16 * Crypto.Ripemd160.r[i]!) (16 * Crypto.Ripemd160.rP[i]! + 8)
          Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          a c b e d sf rest hstd hshift
  · cases phase
    · simpa only [roundOps, h] using
        PackedProbeBridge1.bodyEven1_stepFrame memAt
          (16 * Crypto.Ripemd160.r[i]!) (16 * Crypto.Ripemd160.rP[i]! + 8)
          Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          a b c d e sf rest hstd hshift
    · simpa only [roundOps, h] using
        PackedProbeOdd1.bodyOdd1_stepFrame memAt
          (16 * Crypto.Ripemd160.r[i]!) (16 * Crypto.Ripemd160.rP[i]! + 8)
          Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          a c b e d sf rest hstd hshift
  · cases phase
    · simpa only [roundOps, h] using
        PackedProbeBridge2.bodyEven2_stepFrame memAt
          (16 * Crypto.Ripemd160.r[i]!) (16 * Crypto.Ripemd160.rP[i]! + 8)
          Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          a b c d e sf rest hstd hshift
    · simpa only [roundOps, h] using
        PackedProbeOdd2.bodyOdd2_stepFrame memAt
          (16 * Crypto.Ripemd160.r[i]!) (16 * Crypto.Ripemd160.rP[i]! + 8)
          Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          a c b e d sf rest hstd hshift
  · cases phase
    · simpa only [roundOps, h] using
        PackedProbeBridge3.bodyEven3_stepFrame memAt
          (16 * Crypto.Ripemd160.r[i]!) (16 * Crypto.Ripemd160.rP[i]! + 8)
          Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          a b c d e sf rest hstd hshift
    · simpa only [roundOps, h] using
        PackedProbeOdd3.bodyOdd3_stepFrame memAt
          (16 * Crypto.Ripemd160.r[i]!) (16 * Crypto.Ripemd160.rP[i]! + 8)
          Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          a c b e d sf rest hstd hshift
  · cases phase
    · simpa only [roundOps, h] using
        PackedProbeBridge4.bodyEven4_stepFrame memAt
          (16 * Crypto.Ripemd160.r[i]!) (16 * Crypto.Ripemd160.rP[i]! + 8)
          Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          a b c d e sf rest hstd hshift
    · simpa only [roundOps, h] using
        PackedProbeOdd4.bodyOdd4_stepFrame memAt
          (16 * Crypto.Ripemd160.r[i]!) (16 * Crypto.Ripemd160.rP[i]! + 8)
          Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          a c b e d sf rest hstd hshift

#print axioms roundOps_emitRound
#print axioms emitted_round_exec

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAllRoundExec
