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

open EvmSemantics.EVM

/-- The modulus integer selected by the EIP-198 padded-input parser. -/
def modulusValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input
    (96 + baseSize input + exponentSize input) (modulusSize input)

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
