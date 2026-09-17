import Challenge.Modexp.Submission.LocalPatch.TransportStep

set_option warningAsError true

/-!
Budget-correct realization of a local macro certificate. This module does not
claim that the reference trace enters a macro only at its entry. The phase/no-
interior-entry obligation must still be supplied by a real patch dispatcher.
-/
namespace Challenge.Modexp.Submission.LocalPatch.Transport

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof

/-- A local candidate GasSteps contract with cost at most the source macro's
cost produces the precise new gas surplus. Nothing assumes equal counters,
fixed instruction counts, zero memory expansion, or zero initial memory. -/
theorem discounted_macro {source final : State} (candidate : ByteArray)
    (sourceCost credit startCounter endCounter : Nat)
    (hbudget : sourceCost ≤ source.gasAvailable)
    (hdebit : final.gasAvailable = source.gasAvailable - sourceCost)
    (candidateTrace : GasSteps (liftState candidate 0 startCounter source)
      (liftState candidate 0 endCounter final))
    (hcost : candidateTrace.cost ≤ sourceCost) :
    Steps (liftState candidate credit startCounter source)
      (liftState candidate (credit + (sourceCost - candidateTrace.cost)) endCounter final) := by
  have hcan : candidateTrace.cost ≤ source.gasAvailable + credit := by omega
  have h := candidateTrace.trace (source.gasAvailable + credit) hcan
  have hstart : withGas (liftState candidate 0 startCounter source)
      (source.gasAvailable + credit) = liftState candidate credit startCounter source := rfl
  have hgas : source.gasAvailable + credit - candidateTrace.cost =
      final.gasAvailable + (credit + (sourceCost - candidateTrace.cost)) := by omega
  have hend : withGas (liftState candidate 0 endCounter final)
      (source.gasAvailable + credit - candidateTrace.cost) =
      liftState candidate (credit + (sourceCost - candidateTrace.cost)) endCounter final := by
    rw [hgas]
    rfl
  rw [hstart, hend] at h
  exact h

/-- Re-enter the synchronized relation after a closed macro, once the actual
reference macro has established its final gas debit and fixed-world invariant. -/
theorem discounted_macro_related {reference candidate : ByteArray}
    {source final : State} (sourceCost credit startCounter endCounter : Nat)
    (hworld : FixedWorld reference final)
    (hbudget : sourceCost ≤ source.gasAvailable)
    (hdebit : final.gasAvailable = source.gasAvailable - sourceCost)
    (candidateTrace : GasSteps (liftState candidate 0 startCounter source)
      (liftState candidate 0 endCounter final))
    (hcost : candidateTrace.cost ≤ sourceCost) :
    ∃ targetFinal : State,
      Steps (liftState candidate credit startCounter source) targetFinal ∧
      Related reference candidate final targetFinal := by
  refine ⟨liftState candidate (credit + (sourceCost - candidateTrace.cost)) endCounter final,
    discounted_macro candidate sourceCost credit startCounter endCounter
      hbudget hdebit candidateTrace hcost, ?_⟩
  exact ⟨hworld, credit + (sourceCost - candidateTrace.cost), endCounter, rfl⟩

end Challenge.Modexp.Submission.LocalPatch.Transport
