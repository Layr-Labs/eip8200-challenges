import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Tail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Tail
open EvmSemantics YulEvmCompiler Challenge.EvmProof Paired80WordRound
theorem tail_read_writeWord (memory : ByteArray) (address : Nat) (value : UInt256) :
    MachineState.readWord (writeWord memory address value) address = value :=
  Memory.readWord_writeWord memory address value

theorem tail_read_writeWord_disjoint (memory : ByteArray) (readStart writeStart : Nat)
    (value : UInt256)
    (hdisjoint : readStart + 32 ≤ writeStart ∨ writeStart + 32 ≤ readStart) :
    MachineState.readWord (writeWord memory writeStart value) readStart =
      MachineState.readWord memory readStart := by
  apply Memory.readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hdisjoint

theorem tail_read_results (memory : ByteArray) (q : WordLane) :
    MachineState.readWord (resultMemory memory q) 832 = result0 memory q ∧
    MachineState.readWord (resultMemory memory q) 864 = result1 memory q ∧
    MachineState.readWord (resultMemory memory q) 896 = result2 memory q ∧
    MachineState.readWord (resultMemory memory q) 928 = result3 memory q ∧
    MachineState.readWord (resultMemory memory q) 960 = result4 memory q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals simp (discharger := omega)
    [resultMemory, tail_read_writeWord, tail_read_writeWord_disjoint]

theorem tail_readPadded_writeWord_disjoint (memory : ByteArray)
    (readStart readSize writeStart : Nat) (value : UInt256)
    (hdisjoint : readStart + readSize ≤ writeStart ∨ writeStart + 32 ≤ readStart) :
    MachineState.readPadded (writeWord memory writeStart value) readStart readSize =
      MachineState.readPadded memory readStart readSize := by
  apply Memory.readPadded_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hdisjoint

theorem tail_readPadded_outside (memory : ByteArray) (q : WordLane) (address size : Nat)
    (houtside : address + size ≤ 832 ∨ 992 ≤ address) :
    MachineState.readPadded (resultMemory memory q) address size =
      MachineState.readPadded memory address size := by
  simp (discharger := omega) [resultMemory, tail_readPadded_writeWord_disjoint]

theorem tail_getD_writeWord_outside (memory : ByteArray) (readAt writeAt : Nat)
    (value : UInt256) (houtside : readAt < writeAt ∨ writeAt + 32 ≤ readAt) :
    (writeWord memory writeAt value)[readAt]?.getD 0 = memory[readAt]?.getD 0 := by
  simp only [writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega)]

theorem tail_getD_outside (memory : ByteArray) (q : WordLane) (address : Nat)
    (houtside : address < 832 ∨ 992 ≤ address) :
    (resultMemory memory q)[address]?.getD 0 = memory[address]?.getD 0 := by
  simp (discharger := omega) [resultMemory, tail_getD_writeWord_outside]

theorem tail_writeWord_size (memory : ByteArray) (address : Nat) (value : UInt256) :
    (writeWord memory address value).size = max memory.size (address + 32) := by
  simp only [writeWord, MachineState.writeBytes_size,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    if_neg (by decide : (32 : Nat) ≠ 0)]

theorem tail_resultMemory_size (memory : ByteArray) (q : WordLane) :
    (resultMemory memory q).size = max memory.size 992 := by
  simp only [resultMemory, tail_writeWord_size]
  omega

theorem tail_resultMemory_size_of_ge (memory : ByteArray) (q : WordLane)
    (hsize : 992 ≤ memory.size) : (resultMemory memory q).size = memory.size := by
  rw [tail_resultMemory_size, Nat.max_eq_left hsize]

theorem tail_combine_normalized (memory : ByteArray) (address : Nat) (left right : UInt256) :
    combineWord memory address left right =
      Challenge.EvmProof.Word.ofUInt32
        (Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory address) +
          (Challenge.EvmProof.Word.toUInt32 (UInt256.shiftRight right (UInt256.ofNat 80)) +
            Challenge.EvmProof.Word.toUInt32 left)) := by
  unfold combineWord
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm]
  change Challenge.EvmProof.Word.mask32
    (MachineState.readWord memory address +
      (UInt256.shiftRight right (UInt256.ofNat 80) + left)) = _
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32,
    Challenge.EvmProof.Word.toUInt32_add, Challenge.EvmProof.Word.toUInt32_add]

/-- Hash extraction is valid even when the final packed registers retain garbage. -/
theorem hashAt_resultMemory (memory : ByteArray) (q : WordLane)
    (h : Compression.HashState)
    (hh : StackMemory.hashAt memory = Compression.embedHash h) :
    StackMemory.hashAt (resultMemory memory q) =
      Compression.embedHash (Paired80Compression.combine h q) := by
  have h0 := congrArg Compression.EvmHashState.h0 hh
  have h1 := congrArg Compression.EvmHashState.h1 hh
  have h2 := congrArg Compression.EvmHashState.h2 hh
  have h3 := congrArg Compression.EvmHashState.h3 hh
  have h4 := congrArg Compression.EvmHashState.h4 hh
  simp only [StackMemory.hashAt, Compression.embedHash] at h0 h1 h2 h3 h4
  obtain ⟨r0, r1, r2, r3, r4⟩ := tail_read_results memory q
  simp only [StackMemory.hashAt, r0, r1, r2, r3, r4, result0, result1, result2,
    result3, result4, tail_combine_normalized, h0, h1, h2, h3, h4,
    Word.toUInt32_ofUInt32]
  rfl

#print axioms hashAt_resultMemory

#print axioms tail_read_results
#print axioms tail_readPadded_outside
#print axioms tail_combine_normalized
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Tail
