import Challenge.Modexp.Submission.Proofs.Bytecode.WindowMath
import Challenge.EvmProof.Memory

set_option warningAsError true

/-!
# Four-bit window table memory

Artifact-independent definitions and recurrence lemmas for the sixteen-word
lookup table.  Concrete EVM traces consume these lemmas without unfolding the
complete table construction.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

open EvmSemantics
open EvmSemantics.EVM

def storeWord (memory : ByteArray) (offset : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32)
    offset

def tableMemoryThrough (base modulus : UInt256) (count : Nat) : ByteArray :=
  (List.range count).foldl
    (fun memory index => storeWord memory (32 * index)
      (WindowMath.tableWord base modulus index)) ByteArray.empty

def tableMemory (base modulus : UInt256) : ByteArray :=
  tableMemoryThrough base modulus 16

theorem tableMemoryThrough_succ (base modulus : UInt256) (count : Nat) :
    tableMemoryThrough base modulus (count + 1) =
      storeWord (tableMemoryThrough base modulus count) (32 * count)
        (WindowMath.tableWord base modulus count) := by
  simp [tableMemoryThrough, List.range_succ, List.foldl_append]

theorem activeWordsAfter_table (power : Nat) :
    MachineState.activeWordsAfter (power + 1) (32 * (power + 1)) 32 =
      power + 2 := by
  simp [MachineState.activeWordsAfter]
  omega

theorem activeWordsAfter_lookup (index : Nat) (hindex : index < 16) :
    MachineState.activeWordsAfter 16 (32 * index) 32 = 16 := by
  simp [MachineState.activeWordsAfter]
  omega

theorem readPadded_storeWord (memory : ByteArray) (offset : Nat)
    (word : UInt256) :
    MachineState.readPadded (storeWord memory offset word) offset 32 =
      Data.Bytes.natToBytesPadded word.toNat 32 := by
  unfold storeWord
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using
    Challenge.EvmProof.Memory.readPadded_writeBytes_same memory
      (Data.Bytes.natToBytesPadded word.toNat 32) offset

theorem readWord_storeWord (memory : ByteArray) (offset : Nat)
    (word : UInt256) :
    MachineState.readWord (storeWord memory offset word) offset = word := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory offset word

theorem readWord_tableMemoryThrough (base modulus : UInt256)
    (count index : Nat) (hindex : index < count) :
    MachineState.readWord (tableMemoryThrough base modulus count)
        (32 * index) = WindowMath.tableWord base modulus index := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [show count + 1 = count + 1 by rfl,
        tableMemoryThrough_succ]
      by_cases hlast : index = count
      · subst index
        exact readWord_storeWord _ _ _
      · rw [show storeWord (tableMemoryThrough base modulus count)
              (32 * count) (WindowMath.tableWord base modulus count) =
            MachineState.writeBytes (tableMemoryThrough base modulus count)
              (Data.Bytes.natToBytesPadded
                (WindowMath.tableWord base modulus count).toNat 32)
              (32 * count) by rfl,
          Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega)
        · left
          omega

theorem readWord_tableMemory (base modulus : UInt256) (index : Nat)
    (hindex : index < 16) :
    MachineState.readWord (tableMemory base modulus) (32 * index) =
      WindowMath.tableWord base modulus index := by
  exact readWord_tableMemoryThrough base modulus 16 index hindex

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory
