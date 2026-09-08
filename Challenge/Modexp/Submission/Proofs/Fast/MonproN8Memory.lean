import Challenge.Modexp.Submission.Proofs.Fast.MonproCore

set_option warningAsError true

/-! Memory contracts for the n=8 fixed-offset row with eager T[8] write.
The machine trace must establish these exact boundaries; no arithmetic,
aliasing or inverse hypothesis is added to the incumbent row contract.
This module is not a replacement for the execution/full-call witness. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.MonproN8
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

/-- Both middle writes are invisible outside [8192,8256). -/
theorem readWord_midMem (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 8192 ∨ 8256 ≤ addr) :
    MachineState.readWord (midMem mem c) addr = MachineState.readWord mem addr := by
  unfold midMem midMem1
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
    omega
  · simp [Data.Bytes.natToBytesPadded, ByteArray.size]
    omega

/-- Computing mu after the eager middle writes uses exactly the old mu. -/
theorem rowMu_midMem8 (mem : ByteArray) (c : UInt256) :
    rowMu (midMem mem c) 8 = rowMu mem 8 := by
  unfold rowMu
  rw [readWord_midMem mem c 9376 (by omega),
      readWord_midMem mem c (8224 + 32 * 8) (by omega)]

/-- The direct rowC0 kernel retains the incumbent arbitrary-MINV contract. -/
theorem rowC0_midMem8 (mem : ByteArray) (c : UInt256) :
    rowC0 (midMem mem c) 8 = rowC0 mem 8 := by
  unfold rowC0
  rw [readWord_midMem mem c (32 * 8 - 32) (by omega), rowMu_midMem8]

/-- Eager middle synchronization removes the deferred-store commutation
obligation: L2 starts with precisely rowMid, not a related scratch memory. -/
def eagerRowL2 (mem : ByteArray) (pa pb i : Nat) : MacState :=
  let mid := rowMid mem pa pb 8 i
  l2Step mid (rowMu mid 8) (rowC0 mid 8) 8 7

theorem eagerRowL2_eq (mem : ByteArray) (pa pb i : Nat) :
    eagerRowL2 mem pa pb i = rowL2 mem pa pb 8 i := by
  unfold eagerRowL2 rowL2
  simp only [rowMid, rowMu_midMem8, rowC0_midMem8]

/-- Full scratch memory, not merely the represented Montgomery value. -/
theorem eagerRowMem_eq (mem : ByteArray) (pa pb i : Nat) :
    tailMem (eagerRowL2 mem pa pb i).memory (eagerRowL2 mem pa pb i).carry =
      rowMem mem pa pb 8 i := by
  rw [eagerRowL2_eq]
  rfl

/-- Every fixed-offset first-pass MAC has exactly the incumbent transition. -/
theorem l1Step8_succ (mem : ByteArray) (bi : UInt256) (pa j : Nat) :
    l1Step mem bi pa 8 (j + 1) =
      let prev := l1Step mem bi pa 8 j
      let x := MachineState.readWord prev.memory (pa + 32 * (7 - j))
      let t := MachineState.readWord prev.memory (8256 + 32 * (7 - j))
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded (macSum x bi t prev.carry).toNat 32)
          (8256 + 32 * (7 - j))
        carry := macCarry x bi t prev.carry } := by
  rfl

/-- Every shifted second-pass MAC has exactly the incumbent transition. -/
theorem l2Step8_succ (mem : ByteArray) (mu c0 : UInt256) (k : Nat) :
    l2Step mem mu c0 8 (k + 1) =
      let prev := l2Step mem mu c0 8 k
      let x := MachineState.readWord prev.memory (32 * (6 - k))
      let t := MachineState.readWord prev.memory (8256 + 32 * (6 - k))
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded (macSum x mu t prev.carry).toNat 32)
          (8256 + 32 * (7 - k))
        carry := macCarry x mu t prev.carry } := by
  rfl

end Challenge.Modexp.Submission.Proofs.Fast.MonproN8
