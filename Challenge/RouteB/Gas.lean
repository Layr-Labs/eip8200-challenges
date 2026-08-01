import Challenge.RouteB.Execution
set_option warningAsError true
/-!
# Gas-parametric direct EVM traces

Functional bytecode proofs should not carry a growing nest of subtractions
through every symbolic state.  `GasSteps s t` records a finite trace between
two gas-erased states together with a sufficient budget.  It guarantees the
same trace from every larger budget and records only the remaining gas at the
end.  Costs compose by addition, including through input-dependent loops.
-/

namespace Challenge.RouteB

open EvmSemantics
open EvmSemantics.EVM

/-- Replace only the available gas of an EVM state. -/
def withGas (s : State) (gas : Nat) : State := { s with gasAvailable := gas }

@[simp] theorem withGas_gasAvailable (s : State) (gas : Nat) :
    (withGas s gas).gasAvailable = gas := rfl

@[simp] theorem withGas_withGas (s : State) (g h : Nat) :
    withGas (withGas s g) h = withGas s h := by
  cases s
  rfl

/-- A direct EVM trace uniform in all sufficiently large initial gas budgets.
The endpoints describe every field except gas; `withGas` supplies the actual
initial and final counters. -/
def GasSteps (s t : State) : Prop :=
  ∃ cost : Nat, ∀ gas : Nat, cost ≤ gas →
    Steps (withGas s gas) (withGas t (gas - cost))

namespace GasSteps

theorem refl (s : State) : GasSteps s s := by
  refine ⟨0, fun gas _ => ?_⟩
  simpa using Steps.refl (withGas s gas)

theorem one {s t : State} (cost : Nat)
    (h : ∀ gas, cost ≤ gas →
      Step (withGas s gas) (withGas t (gas - cost))) :
    GasSteps s t := by
  refine ⟨cost, fun gas hgas => ?_⟩
  exact .trans (h gas hgas) (.refl _)

theorem trans {s t u : State} (hst : GasSteps s t) (htu : GasSteps t u) :
    GasSteps s u := by
  obtain ⟨c₁, h₁⟩ := hst
  obtain ⟨c₂, h₂⟩ := htu
  refine ⟨c₁ + c₂, fun gas hgas => ?_⟩
  have hc₁ : c₁ ≤ gas := by omega
  have hc₂ : c₂ ≤ gas - c₁ := by omega
  have hsub : gas - c₁ - c₂ = gas - (c₁ + c₂) := by omega
  simpa [hsub] using (h₁ gas hc₁).append (h₂ (gas - c₁) hc₂)

theorem iterate {I : Nat → State}
    (body : ∀ i, GasSteps (I i) (I (i + 1))) :
    ∀ n, GasSteps (I 0) (I n)
  | 0 => refl _
  | n + 1 => (iterate body n).trans (by simpa using body n)

theorem iterateBounded {I : Nat → State} (count : Nat)
    (body : ∀ i, i < count → GasSteps (I i) (I (i + 1))) :
    GasSteps (I 0) (I count) := by
  induction count with
  | zero => exact refl _
  | succ count ih =>
      exact (ih (fun i hi => body i (Nat.lt_succ_of_lt hi))).trans
        (body count (Nat.lt_succ_self _))

/-- Forget the explicit final gas counter and expose the ordinary predicate
reachability used by `DirectProof`. -/
theorem toReaches {s t : State} (h : GasSteps s t) :
    ∃ cost, ∀ gas, cost ≤ gas →
      Reaches (fun u => u = withGas s gas)
        (fun u => ∃ remaining, u = withGas t remaining) := by
  obtain ⟨cost, hs⟩ := h
  refine ⟨cost, fun gas hgas u hu => ?_⟩
  subst u
  exact ⟨_, hs gas hgas, gas - cost, rfl⟩

/-- Turn a family of gas-parametric traces to exact halted states into the
submission-facing `EventuallyEvaluates` obligation.  Both `isDone` and
`toResult` ignore the available-gas field, so callers only need to identify
the gas-erased final state once. -/
theorem toEventuallyEvaluates {Input : Type}
    (initial final : Input → State) (expected : Input → ExecutionResult)
    (hsteps : ∀ input, GasSteps (initial input) (final input))
    (hdone : ∀ input, (final input).isDone = true)
    (hresult : ∀ input, (final input).toResult = expected input) :
    EventuallyEvaluates
      (fun input gas => withGas (initial input) gas) expected := by
  intro input
  obtain ⟨cost, htrace⟩ := hsteps input
  refine ⟨cost, fun gas hgas s hs => ?_⟩
  subst s
  refine ⟨withGas (final input) (gas - cost), htrace gas hgas, ?_, ?_⟩
  · change (final input).isDone = true
    exact hdone input
  · change (final input).toResult = expected input
    exact hresult input

end GasSteps

end Challenge.RouteB
