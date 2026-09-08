import Challenge.Modexp.Submission.Proofs.Fast.MonproRowModel
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.Monpro

open EvmSemantics EvmSemantics.EVM YulEvmCompiler

/-! ## Memory preservation

Every word `MONPRO` writes lies in `[8192, 9280)`: the `CALLDATACOPY` prologue
writes `64 + 32 * n ≤ 1088` bytes from `8192`, and every limb store lands at
`8256 + 32 * (n - 1 - j) ≤ 9248`.  So every word below `T_ = 0x2000` — that is
every named block `M`, `ACC`, `BASE`, `ONE`, `R1`, `CC`, `RR`, `SUBB` of the
memory map — and every word at or above `9280` — `V_S32 = 9344`,
`V_MINV = 9376`, `V_ML = 9408`, `V_TL = 9440`, `V_EOFF`, `V_N` — survive the
subroutine unchanged. -/

theorem readWord_writeLimb (mem : ByteArray) (w dst addr : Nat)
    (hdstLo : 8192 ≤ dst) (hdstHi : dst + 32 ≤ 9280)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) dst) addr =
      MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega

theorem readWord_l1Step (mem : ByteArray) (bi : UInt256) (pa n addr j : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (l1Step mem bi pa n j).memory addr =
      MachineState.readWord mem addr := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [l1Step]
      rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]
      exact ih

theorem readWord_l2Step (mem : ByteArray) (mu c0 : UInt256) (n addr k : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (l2Step mem mu c0 n k).memory addr =
      MachineState.readWord mem addr := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [l2Step]
      rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]
      exact ih

theorem readWord_midMem1 (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (midMem1 mem c) addr = MachineState.readWord mem addr := by
  simp only [midMem1]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]

theorem readWord_midMem (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (midMem mem c) addr = MachineState.readWord mem addr := by
  simp only [midMem]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr,
    readWord_midMem1 _ _ _ haddr]

theorem readWord_tailMem1 (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (tailMem1 mem c) addr = MachineState.readWord mem addr := by
  simp only [tailMem1]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]

theorem readWord_tailMem (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (tailMem mem c) addr = MachineState.readWord mem addr := by
  simp only [tailMem]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr,
    readWord_tailMem1 _ _ _ haddr]

theorem readWord_rowMid (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowMid mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  simp only [rowMid, rowL1]
  rw [readWord_midMem _ _ _ haddr, readWord_l1Step _ _ _ _ _ _ hn haddr]

theorem readWord_rowMem (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowMem mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  simp only [rowMem, rowL2]
  rw [readWord_tailMem _ _ _ haddr, readWord_l2Step _ _ _ _ _ _ hn haddr,
    readWord_rowMid _ _ _ _ _ _ hn haddr]

theorem readWord_rowsMem (mem : ByteArray) (pa pb n addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) : ∀ i,
    MachineState.readWord (rowsMem mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [rowsMem, readWord_rowMem _ _ _ _ _ _ hn haddr]
      exact ih

theorem readWord_mpZeroed (s : State) (mem : ByteArray) (n addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (mpZeroed s mem n) addr = MachineState.readWord mem addr := by
  simp only [mpZeroed]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega

end Challenge.Modexp.Submission.Proofs.Fast.Monpro

