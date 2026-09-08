import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessPreservation
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineMemory

open EvmSemantics PackedGapInvariant PackedPreprocessPreservation

/-- Five ordered hash stores. Values are already computed by the caller. -/
def writeHash (memory : ByteArray) (v0 v1 v2 v3 v4 : UInt256) : ByteArray :=
  storeWord (storeWord (storeWord (storeWord (storeWord memory 352 v0)
    384 v1) 416 v2) 448 v3) 480 v4

/-- Actual sequential writes preserve all words in the input region. This
does not assert that any instruction sequence executes these writes. -/
theorem writeHash_read_above (memory : ByteArray) (v0 v1 v2 v3 v4 : UInt256)
    (readStart : Nat) (hread : 512 ≤ readStart) :
    MachineState.readWord (writeHash memory v0 v1 v2 v3 v4) readStart =
      MachineState.readWord memory readStart := by
  unfold writeHash
  rw [readWord_storeWord_above _ 480 readStart _ (by omega),
    readWord_storeWord_above _ 448 readStart _ (by omega),
    readWord_storeWord_above _ 416 readStart _ (by omega),
    readWord_storeWord_above _ 384 readStart _ (by omega),
    readWord_storeWord_above _ 352 readStart _ (by omega)]

#print axioms writeHash_read_above

private theorem read_same (memory : ByteArray) (address : Nat) (value : UInt256) :
    MachineState.readWord (storeWord memory address value) address = value :=
  Challenge.EvmProof.Memory.readWord_writeWord memory address value

private theorem read_before (memory : ByteArray) (address readStart : Nat)
    (value : UInt256) (h : readStart + 32 ≤ address) :
    MachineState.readWord (storeWord memory address value) readStart =
      MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  exact Or.inl h

/-- The concrete ascending-store layout exposes precisely the five outputs.
The older StackMemory.storeHash uses a different write order. -/
theorem hashAt_writeHash (memory : ByteArray) (v0 v1 v2 v3 v4 : UInt256) :
    StackMemory.hashAt (writeHash memory v0 v1 v2 v3 v4) =
      { h0 := v0, h1 := v1, h2 := v2, h3 := v3, h4 := v4 } := by
  unfold StackMemory.hashAt writeHash
  rw [read_before _ 480 352 _ (by decide),
    read_before _ 448 352 _ (by decide),
    read_before _ 416 352 _ (by decide),
    read_before _ 384 352 _ (by decide), read_same,
    read_before _ 480 384 _ (by decide),
    read_before _ 448 384 _ (by decide),
    read_before _ 416 384 _ (by decide), read_same,
    read_before _ 480 416 _ (by decide),
    read_before _ 448 416 _ (by decide), read_same,
    read_before _ 480 448 _ (by decide), read_same, read_same]

#print axioms hashAt_writeHash

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineMemory
