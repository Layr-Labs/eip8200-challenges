set_option warningAsError true

/-!
# Message-schedule memory layout

Message word `i` (0 ≤ i < 16) of the current block lives in the 32-byte memory
cell `cell i = 32 * perm i`; the zero sentinel lives in `cell 16 = 512`.
`perm` is the word → cell map of the emitted stores, given by `permTable`:
six disjoint swaps `(2 8)(3 9)(4 10)(5 11)(6 12)(7 13)`, fixing 0, 1, 14, 15;
indices ≥ 16 are fixed. It is an involution, so it is also the cell → word map.

To relocate the schedule again, change `permTable` and the `perm_eval_*`
right-hand sides; every proof in this file is by `decide` over the table.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleLayout

/-- Word → cell table for words 0..15. -/
def permTable : Array Nat := #[0, 1, 8, 9, 10, 11, 12, 13, 2, 3, 4, 5, 6, 7, 14, 15]

/-- Word → cell (equivalently cell → word); identity from 16 on. -/
def perm (i : Nat) : Nat := permTable.getD i i

theorem perm_of_ge {i : Nat} (h : 16 ≤ i) : perm i = i := by
  unfold perm Array.getD
  exact dif_neg (show ¬ i < 16 by omega)

theorem perm_perm_fin : ∀ j : Fin 16, perm (perm j.val) = j.val := by decide

theorem perm_lt_fin : ∀ j : Fin 16, perm j.val < 16 := by decide

theorem perm_perm (i : Nat) : perm (perm i) = i := by
  by_cases h : i < 16
  · exact perm_perm_fin ⟨i, h⟩
  · rw [perm_of_ge (i := i) (by omega), perm_of_ge (i := i) (by omega)]

theorem perm_inj {i j : Nat} (h : perm i = perm j) : i = j := by
  rw [← perm_perm i, h, perm_perm]

theorem perm_lt (i : Nat) (hi : i < 16) : perm i < 16 := perm_lt_fin ⟨i, hi⟩

theorem perm_le (i : Nat) (hi : i ≤ 16) : perm i ≤ 16 := by
  by_cases h : i < 16
  · exact Nat.le_of_lt (perm_lt i h)
  · rw [perm_of_ge (by omega)]
    exact hi

/-- The table form, checked against the emitted stores (word → cell). -/
theorem perm_table :
    (List.range 16).map perm = [0, 1, 8, 9, 10, 11, 12, 13, 2, 3, 4, 5, 6, 7, 14, 15] := by
  decide

@[simp] theorem perm_eval_0 : perm 0 = 0 := by decide
@[simp] theorem perm_eval_1 : perm 1 = 1 := by decide
@[simp] theorem perm_eval_2 : perm 2 = 8 := by decide
@[simp] theorem perm_eval_3 : perm 3 = 9 := by decide
@[simp] theorem perm_eval_4 : perm 4 = 10 := by decide
@[simp] theorem perm_eval_5 : perm 5 = 11 := by decide
@[simp] theorem perm_eval_6 : perm 6 = 12 := by decide
@[simp] theorem perm_eval_7 : perm 7 = 13 := by decide
@[simp] theorem perm_eval_8 : perm 8 = 2 := by decide
@[simp] theorem perm_eval_9 : perm 9 = 3 := by decide
@[simp] theorem perm_eval_10 : perm 10 = 4 := by decide
@[simp] theorem perm_eval_11 : perm 11 = 5 := by decide
@[simp] theorem perm_eval_12 : perm 12 = 6 := by decide
@[simp] theorem perm_eval_13 : perm 13 = 7 := by decide
@[simp] theorem perm_eval_14 : perm 14 = 14 := by decide
@[simp] theorem perm_eval_15 : perm 15 = 15 := by decide
@[simp] theorem perm_eval_16 : perm 16 = 16 := by decide

theorem perm_sixteen : perm 16 = 16 := perm_eval_16

/-- Byte address of the cell holding message word `i` (`i = 16`: the sentinel). -/
def cell (i : Nat) : Nat := 32 * perm i

theorem cell_sixteen : cell 16 = 512 := by decide

theorem cell_le (i : Nat) (hi : i ≤ 16) : cell i ≤ 512 := by
  have := perm_le i hi
  unfold cell
  omega

theorem cell_lt_word (i : Nat) (hi : i < 16) : cell i + 32 ≤ 512 := by
  have := perm_lt i hi
  unfold cell
  omega

/-- Distinct words occupy disjoint cells. -/
theorem cell_disjoint {i j : Nat} (hij : i ≠ j) :
    cell i + 32 ≤ cell j ∨ cell j + 32 ≤ cell i := by
  have hne : perm i ≠ perm j := fun h => hij (perm_inj h)
  unfold cell
  omega

#print axioms perm_of_ge
#print axioms perm_perm
#print axioms perm_inj
#print axioms perm_lt
#print axioms perm_le
#print axioms perm_table
#print axioms perm_sixteen
#print axioms cell_sixteen
#print axioms cell_le
#print axioms cell_lt_word
#print axioms cell_disjoint

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleLayout
