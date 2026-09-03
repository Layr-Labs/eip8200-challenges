import Challenge.EvmProof.Meter

set_option warningAsError true

namespace Challenge.EvmProof.Meter

open EvmSemantics
open EvmSemantics.EVM

/-- Sum index-dependent loop work while telescoping memory-expansion costs. -/
theorem iterateBounded_cost_potential_sum {I : Nat → State}
    (count : Nat) (work : Nat → Nat)
    (body : ∀ j, j < count → GasSteps (I j) (I (j + 1)))
    (hbody : ∀ j (hj : j < count),
      (body j hj).cost + MachineState.memCost (I j).activeWords.toNat =
        work j + MachineState.memCost (I (j + 1)).activeWords.toNat) :
    (GasSteps.iterateBounded count body).cost +
        MachineState.memCost (I 0).activeWords.toNat =
      List.sum ((List.range count).map work) +
        MachineState.memCost (I count).activeWords.toNat := by
  induction count with
  | zero =>
      rw [GasSteps.iterateBounded_zero_cost]
      simp
  | succ count ih =>
      rw [GasSteps.iterateBounded_succ_cost]
      have hprefix := ih
        (body := fun j hj => body j (Nat.lt_succ_of_lt hj))
        (hbody := fun j hj => hbody j (Nat.lt_succ_of_lt hj))
      have hlast := hbody count (Nat.lt_succ_self count)
      simp only [List.range_succ, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega

end Challenge.EvmProof.Meter
