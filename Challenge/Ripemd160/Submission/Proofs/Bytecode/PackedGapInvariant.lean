import Challenge.EvmProof.Memory

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedGapInvariant

open EvmSemantics

/-- The unread-by-stores gap touched by the final right-lane load. -/
def GapZero (memory : ByteArray) : Prop :=
  ∀ i : Nat, 272 ≤ i → i < 280 → memory[i]?.getD 0 = 0

theorem of_size_le (memory : ByteArray) (h : memory.size ≤ 272) :
    GapZero memory := by
  intro i hi _
  exact Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le memory i
    (by omega)

theorem write_disjoint (memory bytes : ByteArray) (start : Nat)
    (h : GapZero memory)
    (hd : start + bytes.size ≤ 272 ∨ 280 ≤ start) :
    GapZero (MachineState.writeBytes memory bytes start) := by
  intro i hi hj
  rw [MachineState.writeBytes_getElem?_getD, if_neg (by omega)]
  exact h i hi hj

theorem spread_store (memory bytes : ByteArray) (k : Nat)
    (h : GapZero memory) (hk : k < 16) (hs : bytes.size = 32) :
    GapZero (MachineState.writeBytes memory bytes (16 * k)) := by
  apply write_disjoint memory bytes (16 * k) h
  left
  omega

theorem high_store (memory bytes : ByteArray) (start : Nat)
    (h : GapZero memory) (hs : 280 ≤ start) :
    GapZero (MachineState.writeBytes memory bytes start) :=
  write_disjoint memory bytes start h (Or.inr hs)

/-- Preservation for an explicit sequence; no assumption about arbitrary memory. -/
theorem write_sequence (writes : List (Nat × ByteArray)) (memory : ByteArray)
    (h : GapZero memory)
    (hd : ∀ p ∈ writes, p.1 + p.2.size ≤ 272 ∨ 280 ≤ p.1) :
    GapZero (writes.foldl (fun m p => MachineState.writeBytes m p.2 p.1) memory) := by
  induction writes generalizing memory with
  | nil => exact h
  | cons p rest ih =>
    apply ih
    · exact write_disjoint memory p.2 p.1 h (hd p (by simp))
    · intro q hq
      exact hd q (by simp [hq])

def storeWord (memory : ByteArray) (address : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded value.toNat 32) address

theorem storeWord_disjoint (memory : ByteArray) (address : Nat) (value : UInt256)
    (h : GapZero memory) (ha : address + 32 ≤ 272 ∨ 280 ≤ address) :
    GapZero (storeWord memory address value) := by
  apply write_disjoint memory _ address h
  simpa [Data.Bytes.natToBytesPadded, ByteArray.size] using ha

/-- Matches the descending store order in the emitted preprocessing region. -/
def spreadWords (words : Nat → UInt256) : Nat → ByteArray → ByteArray
  | 0, memory => memory
  | n + 1, memory => spreadWords words n (storeWord memory (16 * n) (words n))

theorem spreadWords_gap (words : Nat → UInt256) (n : Nat) (hn : n ≤ 16)
    (memory : ByteArray) (h : GapZero memory) :
    GapZero (spreadWords words n memory) := by
  induction n generalizing memory with
  | zero => exact h
  | succ n ih =>
    apply ih (by omega)
    exact storeWord_disjoint memory (16 * n) (words n) h (Or.inl (by omega))

#print axioms spreadWords_gap
#print axioms spread_store
#print axioms write_sequence

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedGapInvariant
