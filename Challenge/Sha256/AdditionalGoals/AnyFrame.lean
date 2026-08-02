import Challenge.Sha256.Spec

set_option warningAsError true

/-!
# Arbitrary-frame strengthening

The minimal specification uses one canonical fresh EVM frame. This optional
goal makes independence from irrelevant caller and world state explicit.
-/

namespace Challenge.Sha256

open EvmSemantics.EVM

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
