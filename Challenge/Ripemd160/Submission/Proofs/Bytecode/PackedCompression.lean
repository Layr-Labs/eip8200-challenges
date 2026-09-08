import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepBounds
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Lifting the packed round to eighty

`PackedStepBounds.correctedStep_represents_final` proves ONE packed round
unconditionally, and `correctedStep_regsOk` proves the step preserves its own
precondition.  Those two together are exactly what a fold needs, so this file
is the induction and nothing else.

## Shape, and why 80 is not 1 repeated

The per-round data varies: the `f` selector is `i / 16`, the two rotation
amounts are `s[i]!` and `sP[i]!`, the message indices are `r[i]!` and `rP[i]!`,
and the constants are `K[i/16]!` and `KP[i/16]!`.  So this is an induction over
a FAMILY of steps.  `correctedStep` is already parameterised on all of them, so
the lift instantiates and never specialises.

## What is deliberately abstract

The packed message words `X` and constants `K` are taken as FAMILIES with
`WordOk` / `ConstOk` hypotheses, not constructed here.  Root owns
`PackedSchedule` and `packedK`; building them here would fork his work.  The
lift is therefore stated against the neutral relations and instantiates when
his schedule lands.

## Mirror of the unpacked development

This is the packed analogue of `StackCompression.leftRounds_represents` /
`rightRounds_represents`, with ONE fold carrying BOTH lines instead of two
folds carrying one each — which is the whole point of the packed
representation.

STATUS: WRITTEN, NOT ELABORATED.  Zero `sorry`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompression

open EvmSemantics
open Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepBounds

/-- One packed register file represents the two unpacked lines at once: lane 0
is the left line, lane 1 is the right line. -/
def RegsRepresents (g : Regs) (yl yr : Working) : Prop :=
  Represents g.a yl.a yr.a ∧ Represents g.b yl.b yr.b ∧
    Represents g.c yl.c yr.c ∧ Represents g.d yl.d yr.d ∧
    Represents g.e yl.e yr.e

/-! ## Rotation-amount side conditions

`StackCompression.leftRotation` / `rightRotation` are `private`, so these are
re-derived.  Same statement, same `interval_cases i <;> decide` proof. -/

private theorem leftRot (i : Nat) (hi : i < 80) :
    0 < Crypto.Ripemd160.s[i]! ∧ Crypto.Ripemd160.s[i]! < 32 := by
  interval_cases i <;> decide

private theorem rightRot (i : Nat) (hi : i < 80) :
    0 < Crypto.Ripemd160.sP[i]! ∧ Crypto.Ripemd160.sP[i]! < 32 := by
  interval_cases i <;> decide

/-! ## The packed fold -/

/-- Round `i`, with every per-round parameter instantiated from the pinned
schedule tables. -/
def packedStep (X K : Nat → UInt256) (i : Nat) (g : Regs) : Regs :=
  correctedStep (i / 16) Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
    g (X i) (K i)

def packedRounds (X K : Nat → UInt256) : Nat → Regs → Regs
  | 0, g => g
  | i + 1, g => packedStep X K i (packedRounds X K i g)

/-- The packed round IS the left line's round and the right line's round,
simultaneously. -/
theorem packedStep_represents (word : Nat → UInt32) (X K : Nat → UInt256)
    (i : Nat) (hi : i < 80) (g : Regs) (yl yr : Working)
    (hrep : RegsRepresents g yl yr) (hregs : RegsOk g)
    (hX : WordOk (X i) (word Crypto.Ripemd160.r[i]!)
      (word Crypto.Ripemd160.rP[i]!))
    (hK : ConstOk (K i) Crypto.Ripemd160.K[i / 16]!
      Crypto.Ripemd160.KP[i / 16]!) :
    RegsRepresents (packedStep X K i g)
      (CompressionCorrect.leftStep word i yl)
      (CompressionCorrect.rightStep word i yr) := by
  have hr : i / 16 < 5 := by omega
  have hl := leftRot i hi
  have hs := rightRot i hi
  exact correctedStep_represents_final (i / 16) Crypto.Ripemd160.s[i]!
    Crypto.Ripemd160.sP[i]! g (X i) (K i)
    yl.a yr.a yl.b yr.b yl.c yr.c yl.d yr.d yl.e yr.e
    (word Crypto.Ripemd160.r[i]!) (word Crypto.Ripemd160.rP[i]!)
    Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]!
    hr hl.1 hl.2 hs.1 hs.2 hrep hregs hX hK

/-- One packed round preserves the step-boundary bounds. -/
theorem packedStep_regsOk (X K : Nat → UInt256) (i : Nat) (hi : i < 80)
    (g : Regs) (hregs : RegsOk g) : RegsOk (packedStep X K i g) :=
  correctedStep_regsOk (i / 16) Crypto.Ripemd160.s[i]!
    Crypto.Ripemd160.sP[i]! g (X i) (K i) (leftRot i hi).2 (rightRot i hi).2
    hregs

/-- **The 80-round lift.**  The packed fold represents BOTH unpacked folds, and
carries the step-boundary invariant with it.  `RegsOk` is in the conclusion
because it is what makes the induction go through — it is not an extra
obligation, it is the induction hypothesis. -/
theorem packedRounds_represents (word : Nat → UInt32) (X K : Nat → UInt256)
    (hX : ∀ i, i < 80 → WordOk (X i) (word Crypto.Ripemd160.r[i]!)
      (word Crypto.Ripemd160.rP[i]!))
    (hK : ∀ i, i < 80 → ConstOk (K i) Crypto.Ripemd160.K[i / 16]!
      Crypto.Ripemd160.KP[i / 16]!)
    (count : Nat) (hc : count ≤ 80) (g : Regs) (yl yr : Working)
    (hrep : RegsRepresents g yl yr) (hregs : RegsOk g) :
    RegsRepresents (packedRounds X K count g)
        (CompressionCorrect.leftRounds word count yl)
        (CompressionCorrect.rightRounds word count yr)
      ∧ RegsOk (packedRounds X K count g) := by
  induction count with
  | zero =>
      simp only [packedRounds, CompressionCorrect.leftRounds,
        CompressionCorrect.rightRounds]
      exact ⟨hrep, hregs⟩
  | succ i ih =>
      have hi : i < 80 := by omega
      obtain ⟨ihrep, ihok⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [packedRounds, CompressionCorrect.leftRounds,
          CompressionCorrect.rightRounds]
        exact packedStep_represents word X K i hi _ _ _ ihrep ihok
          (hX i hi) (hK i hi)
      · rw [packedRounds]
        exact packedStep_regsOk X K i hi _ ihok

/-- The full eighty rounds, as the lift will be used. -/
theorem packedRounds_represents_80 (word : Nat → UInt32) (X K : Nat → UInt256)
    (hX : ∀ i, i < 80 → WordOk (X i) (word Crypto.Ripemd160.r[i]!)
      (word Crypto.Ripemd160.rP[i]!))
    (hK : ∀ i, i < 80 → ConstOk (K i) Crypto.Ripemd160.K[i / 16]!
      Crypto.Ripemd160.KP[i / 16]!)
    (g : Regs) (yl yr : Working)
    (hrep : RegsRepresents g yl yr) (hregs : RegsOk g) :
    RegsRepresents (packedRounds X K 80 g)
      (CompressionCorrect.leftRounds word 80 yl)
      (CompressionCorrect.rightRounds word 80 yr) :=
  (packedRounds_represents word X K hX hK 80 (Nat.le_refl 80) g yl yr
    hrep hregs).1

#print axioms packedStep_represents
#print axioms packedStep_regsOk
#print axioms packedRounds_represents
#print axioms packedRounds_represents_80

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompression
