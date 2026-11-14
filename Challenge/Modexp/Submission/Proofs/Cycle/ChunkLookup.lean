import Mathlib.Data.List.GetD
set_option warningAsError true
universe u
namespace CycleSubmission.ChunkLookup
def valid {α : Type u} : List (List α) → Bool
  | [] => true
  | [xs] => decide (xs.length ≤ 128)
  | xs::ys::rest => decide (xs.length = 128) && valid (ys::rest)
def get? {α : Type u} (chunks : List (List α)) (i : Nat) : Option α :=
  (chunks.getD (i / 128) [])[i % 128]?
theorem get?_eq {α : Type u} (chunks : List (List α)) (h : valid chunks = true) (i : Nat) :
    get? chunks i = chunks.flatten[i]? := by
  induction chunks generalizing i with
  | nil => simp [get?]
  | cons xs tail ih =>
    cases tail with
    | nil =>
      have hlen : xs.length ≤ 128 := of_decide_eq_true h
      by_cases hi : i < 128
      · have hd : i / 128 = 0 := Nat.div_eq_of_lt hi
        have hm : i % 128 = i := Nat.mod_eq_of_lt hi
        simp [get?,hd,hm]
      · have hd : 0 < i / 128 := by omega
        have hn : xs[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        simp only [get?,List.flatten_cons,List.flatten_nil,List.append_nil]
        rw [show i / 128 = (i / 128 - 1) + 1 by omega,List.getD_cons_succ]
        simp [hn]
    | cons ys rest =>
      have hv := Bool.and_eq_true_iff.mp h
      have hlen : xs.length = 128 := of_decide_eq_true hv.1
      by_cases hi : i < 128
      · have hd : i / 128 = 0 := Nat.div_eq_of_lt hi
        have hm : i % 128 = i := Nat.mod_eq_of_lt hi
        simp only [get?,hd,hm,List.getD_cons_zero,List.flatten_cons]
        exact (List.getElem?_append_left (by omega)).symm
      · have hd : i / 128 = (i-128) / 128 + 1 := by omega
        have hm : i % 128 = (i-128) % 128 := by omega
        simp only [get?,hd,hm,List.getD_cons_succ,List.flatten_cons]
        rw [List.getElem?_append_right (by omega),hlen]
        exact ih hv.2 (i-128)
#print axioms get?_eq
end CycleSubmission.ChunkLookup
