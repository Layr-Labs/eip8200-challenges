import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntry

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedMemoryOperands
open EvmSemantics

/-- Reader used by abstract instruction execution on concrete EVM memory. -/
def reader (memory : ByteArray) (address : UInt256) : UInt256 :=
  MachineState.readWord memory address.toNat

theorem reader_ofNat (memory : ByteArray) (address : Nat)
    (h : address < 2 ^ 256) :
    reader memory (UInt256.ofNat address) = MachineState.readWord memory address := by
  unfold reader
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h]

theorem paired_reader (memory : ByteArray) (i j : Nat)
    (hi : i < 16) (hj : j < 16) :
    (reader memory (UInt256.ofNat (16 * i)) |||
      reader memory (UInt256.ofNat (16 * j + 8)))
      = PackedLoadModel.loadPair memory i j := by
  have hl : 16 * i < 2 ^ 256 := by norm_num only [Nat.reducePow]; omega
  have hr : 16 * j + 8 < 2 ^ 256 := by norm_num only [Nat.reducePow]; omega
  rw [reader_ofNat memory _ hl, reader_ofNat memory _ hr]
  rfl

/-- Bounded schedule indices prevent address wrap at every scored round. -/
theorem schedule_reader (memory : ByteArray) (i : Nat) (hi : i < 80) :
    (reader memory (UInt256.ofNat (16 * Crypto.Ripemd160.r[i]!)) |||
      reader memory (UInt256.ofNat (16 * Crypto.Ripemd160.rP[i]! + 8)))
      = PackedLoadModel.loadPair memory Crypto.Ripemd160.r[i]!
          Crypto.Ripemd160.rP[i]! := by
  obtain ⟨hl, hr⟩ := PackedSpreadSchedule.schedule_indices i hi
  exact paired_reader memory _ _ hl hr

/-- Actual post-spread machine operands coincide with the arithmetic model. -/
theorem spread_reader (memory : ByteArray) (words : Nat → UInt256)
    (i : Nat) (hi : i < 80) :
    (reader (PackedGapInvariant.spreadWords words 16 memory)
        (UInt256.ofNat (16 * Crypto.Ripemd160.r[i]!)) |||
      reader (PackedGapInvariant.spreadWords words 16 memory)
        (UInt256.ofNat (16 * Crypto.Ripemd160.rP[i]! + 8)))
      = PackedSpreadSchedule.messageWords memory words i :=
  schedule_reader _ i hi

#print axioms reader_ofNat
#print axioms paired_reader
#print axioms schedule_reader
#print axioms spread_reader
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedMemoryOperands
