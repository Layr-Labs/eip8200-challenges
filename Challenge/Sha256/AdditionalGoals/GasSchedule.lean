import Challenge.Sha256.Spec

set_option warningAsError true

/-!
# Gas-schedule strengthening

The minimal specification asks only for some sufficient gas threshold for each
input. This optional goal exposes a concrete input-size-dependent schedule.
-/

namespace Challenge.Sha256

open EvmSemantics.EVM

/-- The efficiency-carrying strengthening: `schedule n` gas suffices for
every input of `n` bytes. This is what a gas schedule in an EIP would need,
and the top tier of the challenge. -/
def CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ (calldata : ByteArray), CalldataFits calldata → ∀ (g : Nat),
    schedule calldata.size ≤ g →
    Eval (frame code calldata g) (.returned (spec calldata))

/-- A proven gas schedule implies correctness. -/
theorem correct_of_schedule {code : ByteArray} {schedule : Nat → Nat}
    (h : CorrectWithSchedule code schedule) : Correct code :=
  fun calldata hfit =>
    ⟨schedule calldata.size, fun g hg => h calldata hfit g hg⟩

end Challenge.Sha256
