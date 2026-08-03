import Challenge.Sha256.Spec

set_option warningAsError true

/-!
# Gas-schedule strengthening

The minimal specification asks only for some sufficient gas threshold for each
input. This optional goal exposes a concrete input-size-dependent schedule.
-/

namespace Challenge.Sha256

open EvmSemantics.EVM

/-! ## Machine-readable symbolic schedules -/

/-- A small, executable language for gas bounds.  Submissions state their
schedule in this language so the leaderboard can render the *proved function*
as LaTeX instead of trusting a separate, free-form description. -/
inductive GasFormula where
  | calldataSize
  | constant (value : Nat)
  | add (left right : GasFormula)
  | mul (left right : GasFormula)
  | div (numerator : GasFormula) (denominator : Nat)
  | memoryCost (activeWords : GasFormula)

namespace GasFormula

/-- Interpret a symbolic gas formula at an input length. -/
def eval : GasFormula → Nat → Nat
  | .calldataSize, size => size
  | .constant value, _ => value
  | .add left right, n => left.eval n + right.eval n
  | .mul left right, n => left.eval n * right.eval n
  | .div numerator denominator, n => numerator.eval n / denominator
  | .memoryCost activeWords, n =>
      EvmSemantics.MachineState.memCost (activeWords.eval n)

/-- Every schedule expressible by `GasFormula` is monotone in the input size.
In particular, its value at `2^64 - 1` is its worst-case bound over every
admissible calldata length. -/
theorem eval_monotone (formula : GasFormula) : Monotone formula.eval := by
  induction formula with
  | calldataSize =>
      intro left right hle
      exact hle
  | constant value =>
      intro left right hle
      exact le_rfl
  | add left right leftIH rightIH =>
      intro a b hab
      exact Nat.add_le_add (leftIH hab) (rightIH hab)
  | mul left right leftIH rightIH =>
      intro a b hab
      exact Nat.mul_le_mul (leftIH hab) (rightIH hab)
  | div numerator denominator numeratorIH =>
      intro a b hab
      exact Nat.div_le_div_right (numeratorIH hab)
  | memoryCost activeWords activeWordsIH =>
      intro a b hab
      have hwords := activeWordsIH hab
      simp only [eval, EvmSemantics.MachineState.memCost]
      exact Nat.add_le_add (Nat.mul_le_mul_left 3 hwords)
        (Nat.div_le_div_right (Nat.pow_le_pow_left hwords 2))

instance (value : Nat) : OfNat GasFormula value where
  ofNat := .constant value

instance : Add GasFormula := ⟨.add⟩
instance : Mul GasFormula := ⟨.mul⟩
instance : HDiv GasFormula Nat GasFormula := ⟨.div⟩

private def parenthesize (needed : Bool) (body : String) : String :=
  if needed then "\\left(" ++ body ++ "\\right)" else body

/-- Render a formula as inline-compatible LaTeX.  Division is natural-number
division, so it is shown with an explicit floor. -/
private def render : GasFormula → Nat → String
  | .calldataSize, _ => "\\mathrm{CALLDATASIZE}"
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

/-- LaTeX used directly by the generated gas leaderboard. -/
def toLatex (formula : GasFormula) : String := formula.render 0

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

end Challenge.Sha256
