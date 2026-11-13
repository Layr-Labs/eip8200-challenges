import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.MemoryPackedOutput
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def store (memory : ByteArray) (address : Nat) (word : UInt32) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def memory (initial : ByteArray) (h : Compression.HashState) : ByteArray :=
  store (store (store (store (store initial 16 h.h4) 12 h.h3) 8 h.h2) 4 h.h1) 0 h.h0

theorem readPadded_eq (initial : ByteArray) (h : Compression.HashState) :
    MachineState.readPadded (memory initial h) 16 32 =
      Data.Bytes.natToBytesPadded
        (PackedOutputMath.pack5 h.h0 h.h1 h.h2 h.h3 h.h4).toNat 32 := by
  have h0 := h.h0.toNat_lt
  have h1 := h.h1.toNat_lt
  have h2 := h.h2.toNat_lt
  have h3 := h.h3.toNat_lt
  have h4 := h.h4.toNat_lt
  apply ByteArray.ext_getElem
  · simp only [Memory.readPadded_size, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hi hj
    have hil : i < 32 := by simpa only [Memory.readPadded_size] using hi
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj,
      Memory.readPadded_getElem?_getD, if_pos hil]
    simp only [memory, store, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, PackedOutputMath.pack5_toNat]
    interval_cases i <;>
      norm_num [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD,
        PackedOutputMath.pack5Nat] <;> congr 1 <;> omega

theorem readWord_eq (initial : ByteArray) (h : Compression.HashState) :
    MachineState.readWord (memory initial h) 16 =
      PackedOutputMath.pack5 h.h0 h.h1 h.h2 h.h3 h.h4 := by
  unfold MachineState.readWord
  rw [readPadded_eq, Memory.bytesToBigEndianNat_natToBytesPadded]
  · exact (Word.word_eq_ofNat_toNat _).symm
  · exact (PackedOutputMath.pack5_lt_pow160 _ _ _ _ _).trans (by norm_num)

#print axioms readPadded_eq
#print axioms readWord_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.MemoryPackedOutput
