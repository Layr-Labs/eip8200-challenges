import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
set_option warningAsError true
set_option maxRecDepth 20000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelCore

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open PairedScheduleMemory

/-- The sentinel pair carried through the block kernel: memory is long enough to
contain cell 16, and all 32 of its bytes are zero.  BOTH halves are needed —
`writeWord_zero_noop` is false without the length. -/
def SentinelOK (memory : ByteArray) : Prop :=
  736 ≤ memory.size ∧ ∀ i, i < 32 → memory[704 + i]?.getD 0 = 0

/-- A byte outside a `writeWord` window is untouched. -/
theorem writeWord_byte_outside (memory : ByteArray) (start a : Nat) (v : UInt256)
    (hout : a < start ∨ start + 32 ≤ a) :
    (writeWord memory start v)[a]?.getD 0 = memory[a]?.getD 0 := by
  have hbsize : (EvmSemantics.Data.Bytes.natToBytesPadded v.toNat 32).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have h := EvmSemantics.MachineState.writeBytes_getElem?_getD memory
    (EvmSemantics.Data.Bytes.natToBytesPadded v.toNat 32) start a
  rw [hbsize] at h
  rw [if_neg (by omega)] at h
  exact h

/-- `writeWord` never shrinks memory. -/
theorem writeWord_size_ge (memory : ByteArray) (start : Nat) (v : UInt256) :
    memory.size ≤ (writeWord memory start v).size := by
  rw [writeWord_size]; omega

/-- A write disjoint from cell 16 preserves the whole pair. -/
theorem sentinel_writeWord_disjoint (memory : ByteArray) (start : Nat) (v : UInt256)
    (hdis : start + 32 ≤ 704 ∨ 736 ≤ start) (h : SentinelOK memory) :
    SentinelOK (writeWord memory start v) := by
  obtain ⟨hsize, hzero⟩ := h
  refine ⟨le_trans hsize (writeWord_size_ge _ _ _), ?_⟩
  intro i hi
  rw [writeWord_byte_outside memory start (704 + i) v (by omega)]
  exact hzero i hi

/-- Every byte a zero `writeWord` lays down is zero. -/
theorem writeWord_zero_byte_inside (memory : ByteArray) (start i : Nat) (hi : i < 32) :
    (writeWord memory start (UInt256.ofNat 0))[start + i]?.getD 0 = 0 := by
  have hbsize : (EvmSemantics.Data.Bytes.natToBytesPadded (UInt256.ofNat 0).toNat 32).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have h := EvmSemantics.MachineState.writeBytes_getElem?_getD memory
    (EvmSemantics.Data.Bytes.natToBytesPadded (UInt256.ofNat 0).toNat 32) start (start + i)
  rw [hbsize] at h
  rw [if_pos (by omega)] at h
  have hz := YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
    (UInt256.ofNat 0).toNat 32 (start + i - start) (by omega)
  rw [hz] at h
  show (EvmSemantics.MachineState.writeBytes memory _ start)[start + i]?.getD 0 = 0
  rw [h]
  simp

/-- The schedule's own model establishes the pair with NO incoming hypothesis:
`normalizedMemory` ends with the zero write at `cell 16`, which both lays down the
32 zero bytes and grows memory to at least 736. -/
theorem sentinel_normalizedMemory (memory : ByteArray) (words : Nat → UInt256) :
    SentinelOK (normalizedMemory memory words) := by
  refine ⟨?_, ?_⟩
  · rw [normalizedMemory_size]; omega
  · intro i hi
    show (writeWord (storeCells (storeCells memory words 8 8) words 0 8)
      (cell 16) (UInt256.ofNat 0))[704 + i]?.getD 0 = 0
    have hcell : cell 16 = 704 := by norm_num [cell]
    rw [← hcell]
    exact writeWord_zero_byte_inside _ (cell 16) i hi


/-- `storeCells` fills cells `first .. first+n-1`.  While those stay at or below
cell 15 (byte 703) they are disjoint from cell 16, so the pair survives. -/
theorem sentinel_storeCells (memory : ByteArray) (words : Nat → UInt256)
    (first : Nat) : ∀ n, first + n ≤ 16 → SentinelOK memory →
      SentinelOK (storeCells memory words first n)
  | 0, _, h => h
  | n + 1, hle, h => by
      rw [storeCells]
      refine sentinel_writeWord_disjoint _ _ _ ?_ (sentinel_storeCells memory words first n (by omega) h)
      left
      have : first + n ≤ 15 := by omega
      simp only [cell]
      omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelCore
