import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessLayout

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessPreservation

open EvmSemantics Challenge.EvmProof PackedGapInvariant PackedPreprocessLayout

/-- The byte-swap scratch stores do not touch the gap. -/
theorem packedBaseMemory_gap (memory : ByteArray) (word0 word1 : UInt256)
    (hgap : GapZero memory) : GapZero (packedBaseMemory memory word0 word1) := by
  apply storeWord_disjoint
  · exact storeWord_disjoint memory 320 (PackedScheduleMath.packed word1)
      hgap (Or.inr (by decide))
  · exact Or.inr (by decide)

theorem readWord_storeWord_above (memory : ByteArray) (address readStart : Nat)
    (value : UInt256) (h : address + 32 ≤ readStart) :
    MachineState.readWord (storeWord memory address value) readStart =
      MachineState.readWord memory readStart := by
  apply Memory.readWord_writeBytes_disjoint
  right
  simpa [Data.Bytes.natToBytesPadded, ByteArray.size] using h

/-- The actual descending stores preserve every word beginning above their
write extent, including all five chaining slots and the input region. -/
theorem spreadWords_read_above (words : Nat → UInt256) (n : Nat) (hn : n ≤ 16)
    (memory : ByteArray) (readStart : Nat) (hread : 272 ≤ readStart) :
    MachineState.readWord (spreadWords words n memory) readStart =
      MachineState.readWord memory readStart := by
  induction n generalizing memory with
  | zero => rfl
  | succ n ih =>
      change MachineState.readWord
        (spreadWords words n (storeWord memory (16 * n) (words n))) readStart = _
      rw [ih (by omega)]
      exact readWord_storeWord_above memory (16 * n) readStart (words n) (by omega)

theorem packedBaseMemory_read_above (memory : ByteArray) (word0 word1 : UInt256)
    (readStart : Nat) (hread : 352 ≤ readStart) :
    MachineState.readWord (packedBaseMemory memory word0 word1) readStart =
      MachineState.readWord memory readStart := by
  unfold packedBaseMemory
  rw [readWord_storeWord_above _ 288 readStart _ (by omega),
    readWord_storeWord_above _ 320 readStart _ (by omega)]

theorem preprocessing_read_above (memory : ByteArray) (word0 word1 : UInt256)
    (readStart : Nat) (hread : 352 ≤ readStart) :
    MachineState.readWord (spreadMemory (packedBaseMemory memory word0 word1))
      readStart = MachineState.readWord memory readStart := by
  unfold spreadMemory
  rw [spreadWords_read_above _ 16 (by decide) _ readStart (by omega)]
  exact packedBaseMemory_read_above memory word0 word1 readStart hread

theorem preprocessing_gap (memory : ByteArray) (word0 word1 : UInt256)
    (hgap : GapZero memory) :
    GapZero (spreadMemory (packedBaseMemory memory word0 word1)) :=
  spreadMemory_gap _ (packedBaseMemory_gap memory word0 word1 hgap)

#print axioms preprocessing_read_above
#print axioms preprocessing_gap

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessPreservation
