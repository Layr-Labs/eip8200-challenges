import Challenge.Ripemd160.AdditionalGoals.GasSchedule
import Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect

set_option warningAsError true

/-!
# Exact gas schedule for the bundled reference

This module exposes the already-proved exact bytecode cost in the symbolic
format consumed by the generated leaderboard.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Gas

open Challenge.Ripemd160
open Challenge.Ripemd160.Reference.Proofs.Bytecode

/-- Symbolic form of the reference gas schedule used by the leaderboard. -/
def gasFormula : GasFormula :=
  let blocks := (GasFormula.calldataSize + 72) / 64
  3877 + 148364 * blocks + 3 * ((GasFormula.calldataSize + 31) / 32) +
    .memoryCost (65 + 2 * blocks)

/-- Exact gas consumed by the bundled reference on an input of `n` bytes. -/
def gasSchedule : Nat → Nat := gasFormula.eval

@[simp] theorem gasSchedule_eq_referenceGasForSize (inputSize : Nat) :
    gasSchedule inputSize = GasCost.referenceGasForSize inputSize := by
  rfl

/-- The displayed schedule is sufficient for every realizable calldata value
of the given length. -/
theorem gasSchedule_correct :
    CorrectWithSchedule referenceBytecode gasSchedule := by
  intro input hfit gas hgas
  exact ReferenceCorrect.reference_correctWithSchedule input hfit gas
    (by simpa using hgas)

end Challenge.Ripemd160.Reference.Proofs.Gas
