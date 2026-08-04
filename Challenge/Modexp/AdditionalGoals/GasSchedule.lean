import Challenge.Modexp.Spec

set_option warningAsError true

/-!
# Gas-schedule strengthening

Unlike the hash challenges, MODEXP cannot use a schedule indexed only by
`CALLDATASIZE`: its execution cost depends on the three lengths encoded in the
calldata header and on whether the padded modulus is zero.  This optional goal
therefore exposes a concrete schedule over the complete calldata value.
-/

namespace Challenge.Modexp

open EvmSemantics
open EvmSemantics.EVM

/-- The modulus integer selected by the EIP-198 padded-input parser. -/
def modulusValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input
    (96 + baseSize input + exponentSize input) (modulusSize input)

/-! ## Machine-readable symbolic schedules -/

/-- A small expression language for calldata-dependent MODEXP gas bounds.
The conditional nodes make the branch structure explicit in generated reports
instead of hiding it in an arbitrary Lean function. -/
inductive GasFormula where
  | calldataSize
  | baseSize
  | exponentSize
  | modulusSize
  | modulusValue
  | constant (value : Nat)
  | add (left right : GasFormula)
  | mul (left right : GasFormula)
  | div (numerator : GasFormula) (denominator : Nat)
  | memoryCost (activeWords : GasFormula)
  | ifZero (condition whenZero whenNonzero : GasFormula)
  | ifLe (condition : GasFormula) (bound : Nat)
      (whenLe whenGt : GasFormula)

namespace GasFormula

/-- Interpret a symbolic schedule on one complete MODEXP calldata value. -/
def eval : GasFormula → ByteArray → Nat
  | .calldataSize, input => input.size
  | .baseSize, input => Challenge.Modexp.baseSize input
  | .exponentSize, input => Challenge.Modexp.exponentSize input
  | .modulusSize, input => Challenge.Modexp.modulusSize input
  | .modulusValue, input => Challenge.Modexp.modulusValue input
  | .constant value, _ => value
  | .add left right, input => left.eval input + right.eval input
  | .mul left right, input => left.eval input * right.eval input
  | .div numerator denominator, input => numerator.eval input / denominator
  | .memoryCost activeWords, input =>
      MachineState.memCost (activeWords.eval input)
  | .ifZero condition whenZero whenNonzero, input =>
      if condition.eval input = 0 then whenZero.eval input
      else whenNonzero.eval input
  | .ifLe condition bound whenLe whenGt, input =>
      if condition.eval input ≤ bound then whenLe.eval input
      else whenGt.eval input

instance (value : Nat) : OfNat GasFormula value where
  ofNat := .constant value

instance : Add GasFormula := ⟨.add⟩
instance : Mul GasFormula := ⟨.mul⟩
instance : HDiv GasFormula Nat GasFormula := ⟨.div⟩

private def parenthesize (needed : Bool) (body : String) : String :=
  if needed then "\\left(" ++ body ++ "\\right)" else body

/-- Render a formula as inline-compatible LaTeX. -/
private def render : GasFormula → Nat → String
  | .calldataSize, _ => "\\mathrm{CALLDATASIZE}"
  | .baseSize, _ => "B"
  | .exponentSize, _ => "E"
  | .modulusSize, _ => "M"
  | .modulusValue, _ => "V_M"
  | .constant value, _ => toString value
  | .add left right, outerPrecedence =>
      parenthesize (outerPrecedence > 1)
        (left.render 1 ++ " + " ++ right.render 1)
  | .mul left right, outerPrecedence =>
      parenthesize (outerPrecedence > 2)
        (left.render 2 ++ " \\cdot " ++ right.render 2)
  | .div numerator denominator, _ =>
      "\\left\\lfloor\\frac{" ++ numerator.render 0 ++ "}{" ++
        toString denominator ++ "}\\right\\rfloor"
  | .memoryCost activeWords, _ =>
      "C_{\\mathrm{mem}}\\left(" ++ activeWords.render 0 ++ "\\right)"
  | .ifZero condition whenZero whenNonzero, _ =>
      "\\begin{cases}" ++ whenZero.render 0 ++ ",&" ++ condition.render 0 ++
        "=0\\\\" ++ whenNonzero.render 0 ++ ",&" ++ condition.render 0 ++
        "\\ne0\\end{cases}"
  | .ifLe condition bound whenLe whenGt, _ =>
      "\\begin{cases}" ++ whenLe.render 0 ++ ",&" ++ condition.render 0 ++
        "\\le" ++ toString bound ++ "\\\\" ++ whenGt.render 0 ++ ",&" ++
        condition.render 0 ++ ">" ++ toString bound ++ "\\end{cases}"

/-- LaTeX used directly by the generated MODEXP gas leaderboard. -/
def toLatex (formula : GasFormula) : String := formula.render 0

end GasFormula

/-- The efficiency-carrying strengthening: `schedule calldata` gas suffices
for that complete valid MODEXP tuple. -/
def CorrectWithSchedule (code : ByteArray)
    (schedule : ByteArray → Nat) : Prop :=
  ∀ (calldata : ByteArray), ValidInput calldata → ∀ (g : Nat),
    schedule calldata ≤ g →
    Eval (initialState code calldata g) (.returned (spec calldata))

/-- A proven gas schedule implies ordinary challenge correctness. -/
theorem correct_of_schedule {code : ByteArray}
    {schedule : ByteArray → Nat}
    (h : CorrectWithSchedule code schedule) : Correct code :=
  fun calldata hvalid =>
    ⟨schedule calldata, fun g hg => h calldata hvalid g hg⟩

end Challenge.Modexp
