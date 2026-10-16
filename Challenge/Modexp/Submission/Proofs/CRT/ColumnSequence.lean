import Challenge.Modexp.Submission.Proofs.CRT.UniformColumns
import Challenge.Modexp.Submission.Proofs.CRT.SeventeenColumns
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace HistoricalSearch.ColumnSequence
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.ColumnMemory
open HistoricalSearch.MixedMontgomery

def states (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256) : Nat → State
  | 0 => s
  | t+1 => let st := states s minv n rest t
    step t st (if t = 0 then UInt256.ofNat 0 else st.stack.headD (UInt256.ofNat 0)) minv n rest

def incoming (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256) (t : Nat) : UInt256 :=
  if t = 0 then UInt256.ofNat 0 else (states s minv n rest t).stack.headD (UInt256.ofNat 0)

def outWords (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256) (t : Nat) :=
  words t (incoming s minv n rest t) minv
    (aRead (states s minv n rest t).memory) n (qRead (states s minv n rest t).memory)

theorem states_succ (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256) (t : Nat) :
    states s minv n rest (t+1) = step t (states s minv n rest t) (incoming s minv n rest t) minv n rest := rfl

theorem a_preserved (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)
    (t : Nat) (ht : t ≤ 17) (i : Nat) (hi : i < 9) :
    aRead (states s minv n rest t).memory i = aRead s.memory i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [states_succ, step_preserves_a t (by omega) _ _ _ _ _ i hi]
    exact ih (by omega)

theorem q_preserved (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)
    (t u : Nat) (htu : t ≤ u) (hu : u ≤ 17) (i : Nat) (hi : i < 9) (hit : i < t) :
    qRead (states s minv n rest u).memory i = qRead (states s minv n rest t).memory i := by
  induction u with
  | zero => omega
  | succ u ih =>
    by_cases he : t = u+1
    · subst t; rfl
    · rw [states_succ, step_preserves_q u (by omega) _ _ _ _ _ i hi (by omega)]
      exact ih (by omega) (by omega)

theorem d_preserved (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)
    (t u : Nat) (htu : t ≤ u) (hu : u ≤ 17) (i : Nat) (hit : i+8 < t) :
    dRead (states s minv n rest u).memory i = dRead (states s minv n rest t).memory i := by
  induction u with
  | zero => omega
  | succ u ih =>
    by_cases he : t = u+1
    · subst t; rfl
    · rw [states_succ, step_preserves_d u (by omega) _ _ _ _ _ i (by omega)]
      exact ih (by omega) (by omega)

theorem next_carry (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)
    (t : Nat) (ht : t < 16) :
    incoming s minv n rest (t+1) = (outWords s minv n rest t).carry := by
  simp only [incoming, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
  rw [states_succ, step_carry t ht]
  rfl

theorem q_set (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)
    (t : Nat) (ht : t < 9) :
    qRead (states s minv n rest 17).memory t = (outWords s minv n rest t).cancel := by
  rw [q_preserved s minv n rest (t+1) 17 (by omega) (by omega) t ht (by omega)]
  rw [states_succ, step_sets_q t ht]
  rfl

theorem d_set (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)
    (t : Nat) (ht : t < 17) (ht8 : 8 ≤ t) :
    dRead (states s minv n rest 17).memory (t-8) = (outWords s minv n rest t).digit := by
  rw [d_preserved s minv n rest (t+1) 17 (by omega) (by omega) (t-8) (by omega)]
  rw [states_succ, step_sets_d t ht ht8]
  rfl

#print axioms a_preserved
#print axioms q_preserved
#print axioms d_preserved
#print axioms next_carry
#print axioms q_set
#print axioms d_set
end HistoricalSearch.ColumnSequence
