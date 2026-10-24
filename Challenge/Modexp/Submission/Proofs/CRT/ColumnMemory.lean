import Challenge.Modexp.Submission.Proofs.CRT.ColumnContracts
import Challenge.Modexp.Submission.Proofs.CRT.CRTMemoryCells
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace HistoricalSearch.ColumnMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.ConcreteArithmetic
open HistoricalSearch.CRTMemoryCells HistoricalSearch.ColumnContracts

def aRead (mem : ByteArray) (i : Nat) : UInt256 := MachineState.readWord mem (768+32*i)
def qRead (mem : ByteArray) (i : Nat) : UInt256 := MachineState.readWord mem (1056+32*i)
def dRead (mem : ByteArray) (i : Nat) : UInt256 := MachineState.readWord mem (1344+32*i)

def words (t : Nat) (carry minv : UInt256) (a n q : Nat → UInt256) : GeneratedColumns.ColumnWords :=
  match t with
  | 0 => GeneratedColumns.col0Words carry modulusWord maskWord minv a n q
  | 1 => GeneratedColumns.col1Words carry modulusWord maskWord minv a n q
  | 2 => GeneratedColumns.col2Words carry modulusWord maskWord minv a n q
  | 3 => GeneratedColumns.col3Words carry modulusWord maskWord minv a n q
  | 4 => GeneratedColumns.col4Words carry modulusWord maskWord minv a n q
  | 5 => GeneratedColumns.col5Words carry modulusWord maskWord minv a n q
  | 6 => GeneratedColumns.col6Words carry modulusWord maskWord minv a n q
  | 7 => GeneratedColumns.col7Words carry modulusWord maskWord minv a n q
  | 8 => GeneratedColumns.col8Words carry modulusWord maskWord minv a n q
  | 9 => GeneratedColumns.col9Words carry modulusWord maskWord minv a n q
  | 10 => GeneratedColumns.col10Words carry modulusWord maskWord minv a n q
  | 11 => GeneratedColumns.col11Words carry modulusWord maskWord minv a n q
  | 12 => GeneratedColumns.col12Words carry modulusWord maskWord minv a n q
  | 13 => GeneratedColumns.col13Words carry modulusWord maskWord minv a n q
  | 14 => GeneratedColumns.col14Words carry modulusWord maskWord minv a n q
  | 15 => GeneratedColumns.col15Words carry modulusWord maskWord minv a n q
  | 16 => GeneratedColumns.col16Words carry modulusWord maskWord minv a n q
  | _ => ⟨UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩

def step (t : Nat) (s : State) (carry minv : UInt256) (n : Nat → UInt256) (rest : List UInt256) : State :=
  match t with
  | 0 => GeneratedColumns.col0Model s modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 1 => GeneratedColumns.col1Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 2 => GeneratedColumns.col2Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 3 => GeneratedColumns.col3Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 4 => GeneratedColumns.col4Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 5 => GeneratedColumns.col5Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 6 => GeneratedColumns.col6Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 7 => GeneratedColumns.col7Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 8 => GeneratedColumns.col8Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 9 => GeneratedColumns.col9Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 10 => GeneratedColumns.col10Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 11 => GeneratedColumns.col11Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 12 => GeneratedColumns.col12Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 13 => GeneratedColumns.col13Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 14 => GeneratedColumns.col14Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 15 => GeneratedColumns.col15Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | 16 => GeneratedColumns.col16Model s carry modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest
  | _ => s

def cells (t : Nat) (w : GeneratedColumns.ColumnWords) : List (Nat × UInt256) :=
  (if t < 9 then [(1056+32*t, w.cancel)] else []) ++
  (if 8 ≤ t then [(1344+32*(t-8), w.digit)] else [])

theorem step_memory (t : Nat) (ht : t < 17) (s : State) (carry minv : UInt256)
    (n : Nat → UInt256) (rest : List UInt256) :
    (step t s carry minv n rest).memory =
      storeCells s.memory (cells t (words t carry minv (aRead s.memory) n (qRead s.memory))) := by
  interval_cases t <;> rfl

theorem step_carry (t : Nat) (ht : t < 16) (s : State) (carry minv : UInt256)
    (n : Nat → UInt256) (rest : List UInt256) :
    (step t s carry minv n rest).stack.headD (UInt256.ofNat 0) =
      (words t carry minv (aRead s.memory) n (qRead s.memory)).carry := by
  interval_cases t <;> rfl

theorem cell_bounds (t : Nat) (ht : t < 17) (w : GeneratedColumns.ColumnWords)
    (c : Nat × UInt256) (hc : c ∈ cells t w) :
    1056 ≤ c.1 ∧ c.1+32 ≤ 1632 := by
  simp [cells] at hc
  rcases hc with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> dsimp <;> omega

theorem step_preserves_a (t : Nat) (ht : t < 17) (s : State) (carry minv : UInt256)
    (n : Nat → UInt256) (rest : List UInt256) (i : Nat) (hi : i < 9) :
    aRead (step t s carry minv n rest).memory i = aRead s.memory i := by
  unfold aRead
  rw [step_memory t ht]
  apply readWord_storeCells
  intro c hc
  have hb := cell_bounds t ht _ c hc
  omega

theorem step_preserves_q (t : Nat) (ht : t < 17) (s : State) (carry minv : UInt256)
    (n : Nat → UInt256) (rest : List UInt256) (i : Nat) (hi : i < 9) (hit : i < t) :
    qRead (step t s carry minv n rest).memory i = qRead s.memory i := by
  unfold qRead
  rw [step_memory t ht]
  apply readWord_storeCells
  intro c hc
  simp [cells] at hc
  rcases hc with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> dsimp <;> omega

theorem step_preserves_d (t : Nat) (ht : t < 17) (s : State) (carry minv : UInt256)
    (n : Nat → UInt256) (rest : List UInt256) (i : Nat) (hi : i+8 < t) :
    dRead (step t s carry minv n rest).memory i = dRead s.memory i := by
  unfold dRead
  rw [step_memory t ht]
  apply readWord_storeCells
  intro c hc
  simp [cells] at hc
  rcases hc with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> dsimp <;> omega

theorem step_sets_q (t : Nat) (ht : t < 9) (s : State) (carry minv : UInt256)
    (n : Nat → UInt256) (rest : List UInt256) :
    qRead (step t s carry minv n rest).memory t =
      (words t carry minv (aRead s.memory) n (qRead s.memory)).cancel := by
  unfold qRead
  rw [step_memory t (by omega)]
  apply storeCells_hit
  · apply List.mem_append_left
    simp only [if_pos ht]
    exact List.mem_singleton.mpr rfl
  · intro c hc
    simp [cells] at hc
    rcases hc with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · right; omega

theorem step_sets_d (t : Nat) (ht : t < 17) (ht8 : 8 ≤ t) (s : State) (carry minv : UInt256)
    (n : Nat → UInt256) (rest : List UInt256) :
    dRead (step t s carry minv n rest).memory (t-8) =
      (words t carry minv (aRead s.memory) n (qRead s.memory)).digit := by
  unfold dRead
  rw [step_memory t ht]
  apply storeCells_hit
  · simp [cells, ht8]
  · intro c hc
    simp [cells] at hc
    rcases hc with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · right; omega
    · exact Or.inl ⟨rfl, rfl⟩

#print axioms step_memory
#print axioms step_carry
#print axioms step_preserves_a
#print axioms step_preserves_q
#print axioms step_preserves_d
#print axioms step_sets_q
#print axioms step_sets_d

end HistoricalSearch.ColumnMemory
