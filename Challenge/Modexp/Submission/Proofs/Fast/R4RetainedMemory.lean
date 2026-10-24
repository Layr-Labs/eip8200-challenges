import Challenge.Modexp.Submission.Proofs.Fast.R4Loop
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
/-! Exact memory bridge for retaining the n=4 squaring constants and omitting repeated zero stores. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.R4RetainedMemory
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open R4Math R4Bridge

def ZeroTN (mem : ByteArray) : Prop :=
  ∀ i, 2080 ≤ i → i < 2112 → mem[i]?.getD 0 = 0

theorem zeroTN_init (mem : ByteArray) :
    ZeroTN (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 0 32) 2080) := by
  intro i hlo hhi
  rw [MachineState.writeBytes_getElem?_getD]
  rw [if_pos (by simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  exact Monpro.natToBytesPadded_zero_byte 32 (i - 2080) (by omega)

theorem zeroTN_store (mem bytes : ByteArray) (start : Nat) (hz : ZeroTN mem)
    (hout : start + bytes.size ≤ 2080 ∨ 2112 ≤ start) :
    ZeroTN (MachineState.writeBytes mem bytes start) := by
  intro i hlo hhi
  rw [MachineState.writeBytes_getElem?_getD, if_neg (by omega)]
  exact hz i hlo hhi

theorem flush_zero_noop (mem : ByteArray) (hsize : 2112 ≤ mem.size) (hz : ZeroTN mem) :
    MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 0 32) 2080 = mem := by
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split_ifs <;> omega
  · intro i hi hj
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hj]
    rw [MachineState.writeBytes_getElem?_getD]
    simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split
    · next h =>
      rw [Monpro.natToBytesPadded_zero_byte 32 (i - 2080) (by omega)]
      exact (hz i (by omega) (by omega)).symm
    · rfl

def fourStores (mem : ByteArray) (W : W5) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
    (MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded W.t0.toNat 32) 2208)
      (Data.Bytes.natToBytesPadded W.t1.toNat 32) 2176)
      (Data.Bytes.natToBytesPadded W.t2.toNat 32) 2144)
      (Data.Bytes.natToBytesPadded W.t3.toNat 32) 2112

theorem fourStores_zero (mem : ByteArray) (W : W5) (hz : ZeroTN mem) :
    ZeroTN (fourStores mem W) := by
  exact zeroTN_store _ _ _ (zeroTN_store _ _ _
    (zeroTN_store _ _ _ (zeroTN_store _ _ _ hz (Or.inr (by decide)))
      (Or.inr (by decide))) (Or.inr (by decide))) (Or.inr (by decide))

theorem fourStores_size (mem : ByteArray) (W : W5) :
    2112 ≤ (fourStores mem W).size := by
  simp [fourStores, MachineState.writeBytes_size,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

theorem fourStores_eq_r4Mem (mem : ByteArray) (W : W5) (hz : ZeroTN mem)
    (ht : W.t4 = UInt256.ofNat 0) :
    fourStores mem W = r4Mem mem W := by
  change fourStores mem W = MachineState.writeBytes (fourStores mem W)
    (Data.Bytes.natToBytesPadded W.t4.toNat 32) 2080
  rw [ht]
  exact (flush_zero_noop _ (fourStores_size mem W) (fourStores_zero mem W hz)).symm

theorem red4_zero (n0 n1 n2 n3 : UInt256) (W : W5) :
    (red4 n0 n1 n2 n3 W).t4 = UInt256.ofNat 0 := by
  unfold red4
  split
  · assumption
  · rfl


def initMemory (mem : ByteArray) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 0 32) 2080

theorem initMemory_read (mem : ByteArray) (address : Nat)
    (hout : address + 32 ≤ 2080 ∨ 2112 ≤ address) :
    MachineState.readWord (initMemory mem) address = MachineState.readWord mem address := by
  unfold initMemory
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact hout

theorem r4Mem_init (mem : ByteArray) (W : W5) :
    r4Mem (initMemory mem) W = r4Mem mem W := by
  apply ByteArray.ext_getElem
  · simp only [r4Mem, initMemory, MachineState.writeBytes_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split_ifs <;> omega
  · intro i hi hj
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hj]
    simp only [r4Mem, initMemory, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split_ifs <;> rfl

theorem rows4r_init (mem : ByteArray) : rows4r (initMemory mem) = rows4r mem := by
  have hr (address : Nat) (h : address + 32 ≤ 2080 ∨ 2112 ≤ address) :=
    initMemory_read mem address h
  simp only [rows4r, r4Final, hr 96 (Or.inl (by decide)), hr 64 (Or.inl (by decide)),
    hr 32 (Or.inl (by decide)), hr 0 (Or.inl (by decide)), hr 2720 (Or.inr (by decide)),
    hr 2208 (Or.inr (by decide)), hr 2176 (Or.inr (by decide)), hr 2144 (Or.inr (by decide)),
    hr 2112 (Or.inr (by decide)), r4Mem_init]

theorem r4Steps_init (k : Nat) (mem : ByteArray) :
    R4Loop.r4Steps (k+1) (initMemory mem) = R4Loop.r4Steps (k+1) mem := by
  rw [R4Loop.r4Steps_succ, R4Loop.r4Steps_succ, rows4r_init]


theorem r4RunMem_init (k : Nat) (mem : ByteArray) (hk : 1 ≤ k) :
    R4Loop.r4RunMem k (initMemory mem) = R4Loop.r4RunMem k mem := by
  cases k with
  | zero => omega
  | succ k => unfold R4Loop.r4RunMem; rw [r4Steps_init]


theorem rows4r_zero (mem : ByteArray) : ZeroTN (rows4r mem) := by
  change ZeroTN (MachineState.writeBytes (fourStores mem _)
    (Data.Bytes.natToBytesPadded (red4 _ _ _ _ _).t4.toNat 32) 2080)
  rw [red4_zero]
  exact zeroTN_init _

end Challenge.Modexp.Submission.Proofs.Fast.R4RetainedMemory
