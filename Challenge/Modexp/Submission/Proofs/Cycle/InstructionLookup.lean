import Mathlib.Data.List.GetD
set_option warningAsError true
universe u
namespace CycleSubmission.InstructionLookup
inductive Table (α : Type u) where
  | leaf (values : List α)
  | node (leftSize : Nat) (left right : Table α)
def Table.flatten {α : Type u} : Table α → List α
  | .leaf values => values
  | .node _ left right => left.flatten ++ right.flatten
def Table.valid {α : Type u} : Table α → Bool
  | .leaf _ => true
  | .node n left right => (decide (left.flatten.length = n) && left.valid) && right.valid
def Table.get? {α : Type u} : Table α → Nat → Option α
  | .leaf values,i => values[i]?
  | .node n left right,i => if i < n then left.get? i else right.get? (i-n)
theorem Table.get?_eq {α : Type u} (t : Table α) (hv : t.valid = true) (i : Nat) :
    t.get? i = t.flatten[i]? := by
  induction t generalizing i with
  | leaf values => rfl
  | node n left right ihl ihr =>
    have hparts := Bool.and_eq_true_iff.mp hv
    have hleft := Bool.and_eq_true_iff.mp hparts.1
    have hlen : left.flatten.length = n := of_decide_eq_true hleft.1
    simp only [Table.get?, Table.flatten]
    by_cases hi : i < n
    · rw [if_pos hi, List.getElem?_append_left (by rw [hlen]; exact hi)]
      exact ihl hleft.2 i
    · rw [if_neg hi, List.getElem?_append_right (by rw [hlen]; exact Nat.le_of_not_gt hi), hlen]
      exact ihr hparts.2 (i-n)
end CycleSubmission.InstructionLookup
