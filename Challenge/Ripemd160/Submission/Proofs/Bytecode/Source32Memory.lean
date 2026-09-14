import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word
import YulEvmCompiler.BytesLemmas

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Memory
open EvmSemantics Challenge.EvmProof

/-- A transparent local spelling of the existing EVM word store. -/
def writeWord (memory : ByteArray) (address : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded value.toNat 32) address

def source32Memory (memory : ByteArray) : ByteArray :=
  writeWord (writeWord memory 56 (UInt256.ofNat 256)) 32 (UInt256.ofNat 128)

def source32Word : UInt256 := UInt256.ofNat (2 ^ 231 + 2 ^ 40)

theorem read32 (memory : ByteArray) :
    MachineState.readWord (source32Memory memory) 32 = UInt256.ofNat 128 := by
  exact Memory.readWord_writeWord _ _ _

theorem frame88 (memory : ByteArray) (a : Nat) (ha : 88 ≤ a) :
    (source32Memory memory)[a]?.getD 0 = memory[a]?.getD 0 := by
  simp only [source32Memory, writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega), if_neg (by omega)]

private theorem byte128 (i : Nat) (hi : i < 32) :
    (Data.Bytes.natToBytesPadded (UInt256.ofNat 128).toNat 32)[i]?.getD 0 =
      if i = 31 then 128 else 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
  have h : ∀ j : Fin 32,
      UInt8.ofNat ((UInt256.ofNat 128).toNat / 256 ^ (32 - 1 - j.val) % 256) =
        if j.val = 31 then 128 else 0 := by decide
  exact h ⟨i, hi⟩

private theorem byte256 (i : Nat) (hi : i < 32) :
    (Data.Bytes.natToBytesPadded (UInt256.ofNat 256).toNat 32)[i]?.getD 0 =
      if i = 30 then 1 else 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
  have h : ∀ j : Fin 32,
      UInt8.ofNat ((UInt256.ofNat 256).toNat / 256 ^ (32 - 1 - j.val) % 256) =
        if j.val = 30 then 1 else 0 := by decide
  exact h ⟨i, hi⟩

private theorem byteSource (i : Nat) (hi : i < 32) :
    (Data.Bytes.natToBytesPadded source32Word.toNat 32)[i]?.getD 0 =
      if i = 3 then 128 else if i = 26 then 1 else 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
  have h : ∀ j : Fin 32,
      UInt8.ofNat (source32Word.toNat / 256 ^ (32 - 1 - j.val) % 256) =
        if j.val = 3 then 128 else if j.val = 26 then 1 else 0 := by decide
  exact h ⟨i, hi⟩

theorem read60_bytes (memory : ByteArray)
    (hzero : ∀ a, 88 ≤ a → a < 92 → memory[a]?.getD 0 = 0)
    (i : Nat) (hi : i < 32) :
    (source32Memory memory)[60 + i]?.getD 0 =
      (Data.Bytes.natToBytesPadded source32Word.toNat 32)[i]?.getD 0 := by
  rw [byteSource i hi]
  simp only [source32Memory, writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  by_cases hfirst : 60 + i < 64
  · rw [if_pos (by omega), byte128 _ (by omega)]
    split_ifs <;> first | rfl | omega
  · rw [if_neg (by omega)]
    by_cases hsecond : 60 + i < 88
    · rw [if_pos (by omega), byte256 _ (by omega)]
      split_ifs <;> first | rfl | omega
    · rw [if_neg (by omega), hzero _ (by omega) (by omega)]
      rw [if_neg (by omega), if_neg (by omega)]

theorem read60 (memory : ByteArray)
    (hzero : ∀ a, 88 ≤ a → a < 92 → memory[a]?.getD 0 = 0) :
    MachineState.readWord (source32Memory memory) 60 = source32Word := by
  have hread : MachineState.readPadded (source32Memory memory) 60 32 =
      MachineState.readPadded (writeWord ByteArray.empty 60 source32Word) 60 32 := by
    apply Memory.readPadded_congr
    intro i hi
    rw [read60_bytes memory hzero i hi]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    rw [if_pos (by omega), Nat.add_sub_cancel_left]
  calc
    MachineState.readWord (source32Memory memory) 60 =
        MachineState.readWord (writeWord ByteArray.empty 60 source32Word) 60 := by
      unfold MachineState.readWord
      rw [hread]
    _ = source32Word := Memory.readWord_writeWord _ _ _

theorem write28_frame60 (memory : ByteArray) (value : UInt256)
    (a : Nat) (ha : 60 ≤ a) :
    (writeWord memory 28 value)[a]?.getD 0 = memory[a]?.getD 0 := by
  simp only [writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega)]

theorem write28_read60 (memory : ByteArray) (value : UInt256) :
    MachineState.readWord (writeWord memory 28 value) 60 =
      MachineState.readWord memory 60 := by
  apply Memory.readWord_writeBytes_disjoint
  right
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

theorem source_afterWrite28_read60 (memory : ByteArray) (value : UInt256)
    (hzero : ∀ a, 88 ≤ a → a < 92 → memory[a]?.getD 0 = 0) :
    MachineState.readWord (writeWord (source32Memory memory) 28 value) 60 = source32Word := by
  rw [write28_read60, read60 memory hzero]

#print axioms read32
#print axioms frame88
#print axioms read60_bytes
#print axioms read60
#print axioms write28_frame60
#print axioms write28_read60
#print axioms source_afterWrite28_read60
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Memory
