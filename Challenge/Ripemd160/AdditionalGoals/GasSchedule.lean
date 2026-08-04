import Challenge.EvmProof.GasFormula
import Challenge.Ripemd160.Spec

set_option warningAsError true

/-!
# Gas-schedule strengthening

The minimal specification asks only for some sufficient gas threshold for each
input. This optional goal exposes a concrete input-size-dependent schedule.
-/

namespace Challenge.Ripemd160

open EvmSemantics.EVM

/-! ## Machine-readable symbolic schedules -/

/-- Compatibility name for the shared symbolic gas language. -/
abbrev GasFormula := Challenge.EvmProof.GasFormula

namespace GasFormula

abbrev calldataSize : GasFormula := Challenge.EvmProof.GasFormula.calldataSize
abbrev constant : Nat → GasFormula := Challenge.EvmProof.GasFormula.constant
abbrev add : GasFormula → GasFormula → GasFormula :=
  Challenge.EvmProof.GasFormula.add
abbrev mul : GasFormula → GasFormula → GasFormula :=
  Challenge.EvmProof.GasFormula.mul
abbrev div : GasFormula → Nat → GasFormula := Challenge.EvmProof.GasFormula.div
abbrev memoryCost : GasFormula → GasFormula :=
  Challenge.EvmProof.GasFormula.memoryCost
abbrev eval : GasFormula → Nat → Nat := Challenge.EvmProof.GasFormula.eval
abbrev toLatex : GasFormula → String := Challenge.EvmProof.GasFormula.toLatex

theorem eval_monotone (formula : GasFormula) : Monotone formula.eval :=
  Challenge.EvmProof.GasFormula.eval_monotone formula

end GasFormula

/-- The efficiency-carrying strengthening: `schedule n` gas suffices for
every input of `n` bytes. This is what a gas schedule in an EIP would need,
and the top tier of the challenge. -/
def CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ (calldata : ByteArray), CalldataFits calldata → ∀ (g : Nat),
    schedule calldata.size ≤ g →
    Eval (initialState code calldata g) (.returned (spec calldata))

/-- A proven gas schedule implies correctness. -/
theorem correct_of_schedule {code : ByteArray} {schedule : Nat → Nat}
    (h : CorrectWithSchedule code schedule) : Correct code :=
  fun calldata hfit =>
    ⟨schedule calldata.size, fun g hg => h calldata hfit g hg⟩

end Challenge.Ripemd160
