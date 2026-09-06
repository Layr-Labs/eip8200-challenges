import Challenge.Modexp.Submission.Proof.YulMem
import Challenge.Modexp.Submission.Proofs.Limbs

set_option warningAsError true

/-!
# The limb view over function-valued memory

`Challenge.Modexp.Submission.Proofs.Limbs` develops the little-endian
256-bit-limb representation of integers over a `ByteArray` memory (via
`MachineState.readWord`).  The Asm machine's memory is instead a *function*
`Nat → UInt8`; this module mirrors that layer on top of
`Challenge.Modexp.Submission.Proof.YulMem`'s algebra of `loadWord`/`storeWord`.

`yLimbs` reads the consecutive EVM words of a region, `RepresentsY` says a
region holds the fixed-width limb encoding of a value, and the lemmas mirror
`Limbs.value_of_represents`, `Limbs.represents_value_unique`, and
`Limbs.represents_iff_value` (reusing all the value-level machinery from
`Limbs`, which is representation-independent).  The store/update lemmas
describe how `storeWord` changes a single limb of a region and leaves
disjoint regions untouched.
-/

namespace Challenge.Modexp.Submission.Proof.YulLimbs

open Challenge.Modexp.Submission.Proofs.Limbs
open Challenge.Modexp.Submission.Proof.YulMem
open YulSemantics.EVM

/-! ## Limbs of a memory region -/

/-- The consecutive little-endian EVM words of the region starting at `base`,
read through the Yul-side `loadWord`. -/
def yLimbs (mem : Nat → UInt8) (base n : Nat) : List Nat :=
  (List.range n).map fun i => (loadWord mem (base + 32 * i)).toNat

@[simp] theorem length_yLimbs (mem : Nat → UInt8) (base n : Nat) :
    (yLimbs mem base n).length = n := by
  simp [yLimbs]

theorem yLimb_lt {mem : Nat → UInt8} {base n digit : Nat}
    (hdigit : digit ∈ yLimbs mem base n) : digit < radix := by
  simp only [yLimbs, List.mem_map] at hdigit
  rcases hdigit with ⟨i, _, rfl⟩
  exact (loadWord mem (base + 32 * i)).isLt.trans_eq (by norm_num [radix])

/-- `mem[base .. base + 32*n]` is the fixed-width limb encoding of `value`.
The explicit range premise rules out truncating high limbs. -/
def RepresentsY (mem : Nat → UInt8) (base n value : Nat) : Prop :=
  value < radix ^ n ∧ yLimbs mem base n = limbDigits n value

theorem value_of_RepresentsY {mem : Nat → UInt8} {base n value : Nat}
    (hrep : RepresentsY mem base n value) :
    Nat.ofDigits radix (yLimbs mem base n) = value := by
  rw [hrep.2, value_limbDigits]

theorem RepresentsY_value_unique {mem : Nat → UInt8} {base n a b : Nat}
    (ha : RepresentsY mem base n a) (hb : RepresentsY mem base n b) : a = b := by
  rw [← value_of_RepresentsY ha, ← value_of_RepresentsY hb]

theorem RepresentsY_iff_value {mem : Nat → UInt8} {base n value : Nat}
    (hvalue : value < radix ^ n) :
    RepresentsY mem base n value ↔
      Nat.ofDigits radix (yLimbs mem base n) = value := by
  constructor
  · exact value_of_RepresentsY
  · intro heq
    refine ⟨hvalue, ?_⟩
    apply Nat.ofDigits_inj_of_len_eq radix_gt_one
    · rw [length_yLimbs, length_limbDigits hvalue]
    · exact fun digit hdigit => yLimb_lt hdigit
    · exact fun digit hdigit => limbDigits_lt hdigit
    · rw [heq, value_limbDigits]

/-! ## Effects of stores on limbs -/

/-- Reading limbs only depends on the words in the region's own range. -/
theorem yLimbs_congr {mem mem' : Nat → UInt8} {base n : Nat}
    (h : ∀ a, base ≤ a → a < base + 32 * n → mem a = mem' a) :
    yLimbs mem base n = yLimbs mem' base n := by
  simp only [yLimbs]
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < n := List.mem_range.mp hi
  rw [loadWord_congr]
  intro a ha1 ha2
  exact h a (by omega) (by omega)

/-- Storing a word at the `i`-th limb slot changes only that limb. -/
theorem yLimbs_storeWord (mem : Nat → UInt8) (base n i : Nat) (_hi : i < n)
    (v : U256) :
    yLimbs (storeWord mem (base + 32 * i) v) base n =
      (yLimbs mem base n).set i v.toNat := by
  apply List.ext_getElem (by simp) (fun j _ _ => ?_)
  by_cases hij : i = j
  · subst hij
    simp only [yLimbs, List.getElem_map, List.getElem_range]
    rw [List.getElem_set_self, loadWord_storeWord_self]
  · simp only [yLimbs, List.getElem_map, List.getElem_range, List.getElem_set,
      if_neg hij]
    congr 1
    exact loadWord_storeWord_disjoint (by omega)

/-- Storing outside a region does not change its limbs. -/
theorem yLimbs_storeWord_disjoint {mem : Nat → UInt8} {base n q : Nat}
    {v : U256} (h : q + 32 ≤ base ∨ base + 32 * n ≤ q) :
    yLimbs (storeWord mem q v) base n = yLimbs mem base n := by
  rw [yLimbs_congr]
  intro a ha1 ha2
  exact storeWord_other mem q v a (by omega)

/-- Storing outside a region does not change what it represents. -/
theorem RepresentsY_storeWord_disjoint {mem : Nat → UInt8} {base n q value : Nat}
    {v : U256} (hrep : RepresentsY mem base n value)
    (h : q + 32 ≤ base ∨ base + 32 * n ≤ q) :
    RepresentsY (storeWord mem q v) base n value :=
  ⟨hrep.1, by rw [yLimbs_storeWord_disjoint h, hrep.2]⟩

theorem RepresentsY_storeByte_disjoint {mem : Nat → UInt8} {base n q value : Nat}
    {v : U256} (hrep : RepresentsY mem base n value)
    (h : q + 32 ≤ base ∨ base + 32 * n ≤ q) :
    RepresentsY (storeByte mem q v) base n value := by
  refine ⟨hrep.1, ?_⟩
  have hcongr : yLimbs (storeByte mem q v) base n = yLimbs mem base n := by
    rw [yLimbs_congr]
    intro a ha1 ha2
    exact storeByte_other mem q v a (by omega)
  rw [hcongr, hrep.2]

/-! ## Zero regions -/

theorem yLimbs_zero (base n : Nat) :
    yLimbs (fun _ => 0) base n = List.replicate n 0 := by
  simp [yLimbs, loadWord_zero]

theorem yLimbs_zero_value (base n : Nat) :
    Nat.ofDigits radix (yLimbs (fun _ => 0) base n) = 0 := by
  rw [yLimbs_zero]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, Nat.ofDigits_cons, ih]
      simp

/-- Fresh (all-zero) memory represents the value `0`. -/
theorem representsY_zero (base n : Nat) : RepresentsY (fun _ => 0) base n 0 := by
  have hpos : 0 < radix ^ n := by
    have := Nat.one_le_pow n radix radix_pos
    omega
  refine ⟨hpos, ?_⟩
  apply Nat.ofDigits_inj_of_len_eq radix_gt_one
  · rw [length_yLimbs, length_limbDigits hpos]
  · intro digit hdigit
    rw [yLimbs_zero] at hdigit
    rcases List.mem_replicate.mp hdigit with ⟨_, rfl⟩
    exact radix_pos
  · intro digit hdigit
    exact limbDigits_lt hdigit
  · rw [yLimbs_zero_value, value_limbDigits]

end Challenge.Modexp.Submission.Proof.YulLimbs
