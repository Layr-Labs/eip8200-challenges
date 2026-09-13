import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixZeroMload
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace AstraPadPrefixCanonical
open EvmSemantics Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode

/-- Identify the previously checked isolated overwrite recursion with the imported
canonical table recursion; no table or memory definition is replaced. -/
theorem storeDescending_eq (memory : ByteArray) (words : Nat → UInt256)
    (first count : Nat) :
    AstraPadPrefixKernel.storeDescending memory words first count =
      StaggerTableMemory.storeDescending memory words first count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    simp only [AstraPadPrefixKernel.storeDescending,
      StaggerTableMemory.storeDescending, ih]
    rfl

/-- Both overlapping source slots must be zero. A zero low slot alone does
not justify replacing the whole 256-bit load by PUSH0. -/
theorem read_table_zero (memory : ByteArray) (words : Nat → UInt256)
    (j : Nat) (hj : 0 < j ∧ j < 61)
    (hleft : words StaggerTableLayout.slots[j]! = UInt256.ofNat 0)
    (hright : words StaggerTableLayout.slots[j-1]! = UInt256.ofNat 0) :
    MachineState.readWord (StaggerTableLayout.resultMemory memory words) (18*j) =
      UInt256.ofNat 0 := by
  have h := AstraPadPrefixKernel.zero_pair_readWord memory
    (StaggerTableLayout.tableWords words) j hj hleft hright
  rw [storeDescending_eq] at h
  exact h

/-- The pad-prefix contract is uniform in the values at slots 0, 14, and 15.
All other schedule slots are zero; certify both halves of an overlapping load. -/
theorem read_pad_table_zero (memory : ByteArray) (words : Nat → UInt256)
    (hpad : ∀ i, i ≠ 0 → i ≠ 14 → i ≠ 15 → words i = UInt256.ofNat 0)
    (j : Nat) (hj : 0 < j ∧ j < 61)
    (hleft : StaggerTableLayout.slots[j]! ≠ 0 ∧
      StaggerTableLayout.slots[j]! ≠ 14 ∧ StaggerTableLayout.slots[j]! ≠ 15)
    (hright : StaggerTableLayout.slots[j-1]! ≠ 0 ∧
      StaggerTableLayout.slots[j-1]! ≠ 14 ∧ StaggerTableLayout.slots[j-1]! ≠ 15) :
    MachineState.readWord (StaggerTableLayout.resultMemory memory words) (18*j) =
      UInt256.ofNat 0 :=
  read_table_zero memory words j hj
    (hpad _ hleft.1 hleft.2.1 hleft.2.2)
    (hpad _ hright.1 hright.2.1 hright.2.2)

/-- Actual EVM MLOAD result, including the unchanged machine-state component. -/
theorem mload_pad_table_zero (state : MachineState) (words : Nat → UInt256)
    (hpad : ∀ i, i ≠ 0 → i ≠ 14 → i ≠ 15 → words i = UInt256.ofNat 0)
    (j : Nat) (hj : 0 < j ∧ j < 61)
    (hleft : StaggerTableLayout.slots[j]! ≠ 0 ∧
      StaggerTableLayout.slots[j]! ≠ 14 ∧ StaggerTableLayout.slots[j]! ≠ 15)
    (hright : StaggerTableLayout.slots[j-1]! ≠ 0 ∧
      StaggerTableLayout.slots[j-1]! ≠ 14 ∧ StaggerTableLayout.slots[j-1]! ≠ 15) :
    let afterTable := {state with memory := StaggerTableLayout.resultMemory state.memory words}
    MachineState.mload afterTable (UInt256.ofNat (18*j)) =
      (UInt256.ofNat 0, afterTable) := by
  dsimp only
  unfold MachineState.mload
  have haddr : (UInt256.ofNat (18*j)).toNat = 18*j := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [haddr, read_pad_table_zero state.memory words hpad j hj hleft hright]

/-- Fresh-frontier list of interior table positions whose two source slots avoid
0, 14, and 15 in the imported canonical layout. -/
def zeroPairPositions : List Nat :=
  [1, 5, 6, 7, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 31, 32, 33, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 58, 59, 60]

/-- Kernel-evaluated certificate, checked against imported slots, not a copied table. -/
theorem zeroPairPositions_complete : ∀ j : Fin 61,
    j.val ∈ zeroPairPositions ↔
      0 < j.val ∧
      (StaggerTableLayout.slots[j.val]! ≠ 0 ∧
       StaggerTableLayout.slots[j.val]! ≠ 14 ∧ StaggerTableLayout.slots[j.val]! ≠ 15) ∧
      (StaggerTableLayout.slots[j.val-1]! ≠ 0 ∧
       StaggerTableLayout.slots[j.val-1]! ≠ 14 ∧ StaggerTableLayout.slots[j.val-1]! ≠ 15) := by
  decide

/-- A directly consumable MLOAD certificate at every certified table position. -/
theorem mload_certified_zero (state : MachineState) (words : Nat → UInt256)
    (hpad : ∀ i, i ≠ 0 → i ≠ 14 → i ≠ 15 → words i = UInt256.ofNat 0)
    (j : Fin 61) (hcert : j.val ∈ zeroPairPositions) :
    let afterTable := {state with memory := StaggerTableLayout.resultMemory state.memory words}
    MachineState.mload afterTable (UInt256.ofNat (18*j.val)) =
      (UInt256.ofNat 0, afterTable) := by
  obtain ⟨hpos, hleft, hright⟩ := (zeroPairPositions_complete j).mp hcert
  exact mload_pad_table_zero state words hpad j.val ⟨hpos, j.isLt⟩ hleft hright

#print axioms zeroPairPositions_complete
#print axioms mload_certified_zero
#print axioms storeDescending_eq
#print axioms read_table_zero
#print axioms read_pad_table_zero
#print axioms mload_pad_table_zero
end AstraPadPrefixCanonical
