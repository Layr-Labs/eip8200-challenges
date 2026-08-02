import Challenge.Sha256.Spec

set_option warningAsError true

/-!
# Stronger SHA-256 challenge predicates

`Spec.lean` contains the minimal correctness statement.  This module keeps
the optional gas-schedule and arbitrary-frame strengthenings out of that
audit surface.
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

/-- The frame-generalized statement: the same conclusion from *any* machine
state that is a fresh frame executing `code` — arbitrary world, caller, call
value, and storage. `Correct` is this restricted to the canonical world; the
gap between them is the noninterference obligation `Obligation.W`. -/
def CorrectInAnyFrame (code : ByteArray) : Prop :=
  ∀ (s : State), s.executionEnv.code = code → s.pc = 0 → s.stack = [] →
    s.callStack = [] → s.halt = .Running → s.memory = .empty →
    s.activeWords = 0 → s.executionEnv.fork = .Osaka →
    Precompile.isPrecompile s.executionEnv.fork s.executionEnv.codeAddr = false →
    CalldataFits s.executionEnv.calldata →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval { s with gasAvailable := g } (.returned (spec s.executionEnv.calldata))

end Challenge.Sha256
