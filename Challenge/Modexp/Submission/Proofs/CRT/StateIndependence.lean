import Challenge.Modexp.Submission.Proofs.CRT.ColumnSequence
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

namespace HistoricalSearch.StateIndependence
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.ColumnMemory HistoricalSearch.ColumnSequence

theorem step_memory_congr (t : Nat) (ht : t < 17) (s s' : State)
    (carry carry' minv : UInt256) (n : Nat → UInt256) (rest rest' : List UInt256)
    (hm : s.memory = s'.memory) (hc : carry = carry') :
    (step t s carry minv n rest).memory = (step t s' carry' minv n rest').memory := by
  rw [step_memory t ht, step_memory t ht, hm, hc]

theorem step_head_congr (t : Nat) (ht : t < 17) (s s' : State)
    (carry carry' minv : UInt256) (n : Nat → UInt256) (rest rest' : List UInt256)
    (hm : s.memory = s'.memory) (hc : carry = carry') :
    (step t s carry minv n rest).stack.headD (UInt256.ofNat 0) =
      (step t s' carry' minv n rest').stack.headD (UInt256.ofNat 0) := by
  by_cases h16 : t < 16
  · rw [step_carry t h16, step_carry t h16, hm, hc]
  · have he : t = 16 := by omega
    subst t
    rfl

/-- Initial stack, pc, environment fields, and saved rest cannot affect the
column memory calculation or any subsequently used carry word. -/
theorem states_memory_head (s s' : State) (minv : UInt256) (n : Nat → UInt256)
    (rest rest' : List UInt256) (hm : s.memory = s'.memory) (t : Nat) (ht : t ≤ 17) :
    (states s minv n rest t).memory = (states s' minv n rest' t).memory ∧
    (0 < t → (states s minv n rest t).stack.headD (UInt256.ofNat 0) =
      (states s' minv n rest' t).stack.headD (UInt256.ofNat 0)) := by
  induction t with
  | zero => exact ⟨hm, by omega⟩
  | succ t ih =>
    have ih' := ih (by omega)
    have hc : incoming s minv n rest t = incoming s' minv n rest' t := by
      unfold incoming
      split
      · rfl
      · exact ih'.2 (by omega)
    rw [states_succ, states_succ]
    exact ⟨step_memory_congr t (by omega) _ _ _ _ minv n rest rest' ih'.1 hc,
      fun _ => step_head_congr t (by omega) _ _ _ _ minv n rest rest' ih'.1 hc⟩

theorem states_memory (s s' : State) (minv : UInt256) (n : Nat → UInt256)
    (rest rest' : List UInt256) (hm : s.memory = s'.memory) :
    (states s minv n rest 17).memory = (states s' minv n rest' 17).memory :=
  (states_memory_head s s' minv n rest rest' hm 17 (by decide)).1

def metadata (s : State) : State := {s with pc := UInt256.ofNat 0, memory := ByteArray.empty, stack := []}

theorem step_metadata (t : Nat) (ht : t < 17) (s : State) (carry minv : UInt256)
    (n : Nat → UInt256) (rest : List UInt256) :
    metadata (step t s carry minv n rest) = metadata s := by
  interval_cases t <;> rfl

theorem states_metadata (s : State) (minv : UInt256) (n : Nat → UInt256)
    (rest : List UInt256) (t : Nat) (ht : t ≤ 17) :
    metadata (states s minv n rest t) = metadata s := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [states_succ, step_metadata t (by omega)]
    exact ih (by omega)

#print axioms states_memory_head
#print axioms states_memory
#print axioms states_metadata
end HistoricalSearch.StateIndependence
