import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def copied (s : State) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (MachineState.readPadded submissionBytecode 106 32) 0
    activeWords := s.activeWordsAfterUInt256 0 32 }

def writeWord (memory : ByteArray) (offset : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded value.toNat 32) offset

theorem literal_bytes : MachineState.readPadded submissionBytecode 106 32 =
    Data.Bytes.natToBytesPadded (PatternedWordData.expectedWordAt 0).toNat 32 := by
  have hprefix : MachineState.readPadded submissionBytecode 106 32 =
      MachineState.readPadded submissionByteChunk0 106 32 := by
    apply Challenge.EvmProof.Memory.readPadded_congr
    intro i hi
    interval_cases i <;> rfl
  rw [hprefix]
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hi hj
    have hlt : i < 32 := by simpa using hi
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hj,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos hlt,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hlt,
      PatternedWordData.expectedWordAt_0]
    interval_cases i <;> decide

theorem copied_word_zero (s : State) : MachineState.readWord (copied s).memory 0 =
    PatternedWordData.expectedWordAt 0 := by
  unfold copied
  rw [literal_bytes]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem copied_word_above (s : State) (address : Nat) (ha : 32 ≤ address) :
    MachineState.readWord (copied s).memory address = MachineState.readWord s.memory address := by
  unfold copied
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  rw [literal_bytes, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega

@[simp] theorem copied_executionEnv (s : State) : (copied s).executionEnv = s.executionEnv := rfl
@[simp] theorem copied_halt (s : State) : (copied s).halt = s.halt := rfl
@[simp] theorem copied_callStack (s : State) : (copied s).callStack = s.callStack := rfl

def hash : Compression.EvmHashState :=
  { h0 := UInt256.ofNat 0x406a6f1a
    h1 := UInt256.ofNat 0x8e85b80c
    h2 := UInt256.ofNat 0x2508f298
    h3 := UInt256.ofNat 0x0d1df121
    h4 := UInt256.ofNat 0x3c0a4ebe }

def hashMemory (memory : ByteArray) : ByteArray :=
  let m0 := writeWord memory 32 hash.h0
  let m1 := writeWord m0 64 hash.h1
  let m2 := writeWord m1 96 hash.h2
  let m3 := writeWord m2 128 hash.h3
  writeWord m3 160 hash.h4

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    memory := hashMemory s.memory
    activeWords := FastEmptyBlock.emptyActiveWords s
    pc := UInt256.ofNat 461
    stack := [DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

private theorem read_same (memory : ByteArray) (offset : Nat) (value : UInt256) :
    MachineState.readWord (writeWord memory offset value) offset = value :=
  Challenge.EvmProof.Memory.readWord_writeWord _ _ _

private theorem read_disjoint (memory : ByteArray) (address offset : Nat) (value : UInt256)
    (h : address + 32 ≤ offset ∨ offset + 32 ≤ address) :
    MachineState.readWord (writeWord memory offset value) address = MachineState.readWord memory address := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using h

theorem resultState_hash (s : State) (input : ByteArray) (i : Nat) :
    StackMemory.hashAt (resultState s input i).memory = hash := by
  unfold resultState hashMemory StackMemory.hashAt
  simp only [read_disjoint _ 32 160 _ (Or.inl (by omega)),
    read_disjoint _ 32 128 _ (Or.inl (by omega)),
    read_disjoint _ 32 96 _ (Or.inl (by omega)),
    read_disjoint _ 32 64 _ (Or.inl (by omega)),
    read_disjoint _ 64 160 _ (Or.inl (by omega)),
    read_disjoint _ 64 128 _ (Or.inl (by omega)),
    read_disjoint _ 64 96 _ (Or.inl (by omega)),
    read_disjoint _ 96 160 _ (Or.inl (by omega)),
    read_disjoint _ 96 128 _ (Or.inl (by omega)),
    read_disjoint _ 128 160 _ (Or.inl (by omega)), read_same]

theorem resultState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (ha : 192 ≤ address) :
    MachineState.readWord (resultState s input i).memory address = MachineState.readWord s.memory address := by
  unfold resultState hashMemory
  rw [read_disjoint _ _ _ _ (Or.inr (by omega)),
    read_disjoint _ _ _ _ (Or.inr (by omega)),
    read_disjoint _ _ _ _ (Or.inr (by omega)),
    read_disjoint _ _ _ _ (Or.inr (by omega)),
    read_disjoint _ _ _ _ (Or.inr (by omega))]

@[simp] theorem resultState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).executionEnv = s.executionEnv := rfl
@[simp] theorem resultState_halt (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).halt = s.halt := rfl
@[simp] theorem resultState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).callStack = s.callStack := rfl


/-! ## Depth-2 ladder rung: `H2` install with block 1 consumed -/

def hash2 : Compression.EvmHashState :=
  { h0 := UInt256.ofNat 0xa7557f9b
    h1 := UInt256.ofNat 0x1ea410e0
    h2 := UInt256.ofNat 0xdb680f80
    h3 := UInt256.ofNat 0xc7f1f365
    h4 := UInt256.ofNat 0x97936109 }

def hashMemory2 (memory : ByteArray) : ByteArray :=
  let m0 := writeWord memory 32 hash2.h0
  let m1 := writeWord m0 64 hash2.h1
  let m2 := writeWord m1 96 hash2.h2
  let m3 := writeWord m2 128 hash2.h3
  writeWord m3 160 hash2.h4

/-- After the two extra word checks the rung installs `H2` and returns to the
driver's `102` continuation with the block-1 offset (`0x40`) on the stack. -/
def resultState2 (s : State) (input : ByteArray) : State :=
  { s with
    memory := hashMemory2 s.memory
    activeWords := FastEmptyBlock.emptyActiveWords s
    pc := UInt256.ofNat 461
    stack := [DriverTrace.blockOffsetWord 1, Padding.paddedWord input] }

theorem resultState2_hash (s : State) (input : ByteArray) :
    StackMemory.hashAt (resultState2 s input).memory = hash2 := by
  unfold resultState2 hashMemory2 StackMemory.hashAt
  simp only [read_disjoint _ 32 160 _ (Or.inl (by omega)),
    read_disjoint _ 32 128 _ (Or.inl (by omega)),
    read_disjoint _ 32 96 _ (Or.inl (by omega)),
    read_disjoint _ 32 64 _ (Or.inl (by omega)),
    read_disjoint _ 64 160 _ (Or.inl (by omega)),
    read_disjoint _ 64 128 _ (Or.inl (by omega)),
    read_disjoint _ 64 96 _ (Or.inl (by omega)),
    read_disjoint _ 96 160 _ (Or.inl (by omega)),
    read_disjoint _ 96 128 _ (Or.inl (by omega)),
    read_disjoint _ 128 160 _ (Or.inl (by omega)), read_same]

theorem resultState2_word_above (s : State) (input : ByteArray) (address : Nat)
    (ha : 192 ≤ address) :
    MachineState.readWord (resultState2 s input).memory address = MachineState.readWord s.memory address := by
  unfold resultState2 hashMemory2
  rw [read_disjoint _ _ _ _ (Or.inr (by omega)),
    read_disjoint _ _ _ _ (Or.inr (by omega)),
    read_disjoint _ _ _ _ (Or.inr (by omega)),
    read_disjoint _ _ _ _ (Or.inr (by omega)),
    read_disjoint _ _ _ _ (Or.inr (by omega))]

@[simp] theorem resultState2_executionEnv (s : State) (input : ByteArray) :
    (resultState2 s input).executionEnv = s.executionEnv := rfl
@[simp] theorem resultState2_halt (s : State) (input : ByteArray) :
    (resultState2 s input).halt = s.halt := rfl
@[simp] theorem resultState2_callStack (s : State) (input : ByteArray) :
    (resultState2 s input).callStack = s.callStack := rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory
