import Challenge.Modexp.Submission.Proofs.Fast.CarryRowModel
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandSnapshot

set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro CarryRowModel

theorem read_row_high (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 8) (ha : 8960 ≤ addr) :
    MachineState.readWord (rowCarry mem pa pb n i) addr = MachineState.readWord mem addr := by
  unfold rowCarry rowL2Carry tailCarry tailMem1
  rw [readWord_storeWord_outside _ _ 8224 addr (by omega),
    readWord_storeWord_outside _ _ 8256 addr (by omega),
    read_l2_high _ _ _ n addr (n-1) hn ha]
  unfold midMem1
  rw [readWord_storeWord_outside _ _ 8224 addr (by omega)]
  unfold rowL1
  exact read_l1_high mem _ pa n addr n hn ha

theorem Snapshot.row {mem : ByteArray} {pa n : Nat} (h : Snapshot mem pa n)
    (pb i : Nat) (hn : n ≤ 8) (hpa : pa+32*n ≤ 8192) :
    Snapshot (rowCarry mem pa pb n i) pa n := by
  intro k hk
  rw [read_row_high _ _ _ _ _ _ hn (by omega),
    readWord_rowCarry _ _ _ _ _ _ (by omega) (Or.inl (by omega))]
  exact h k hk

theorem Snapshot.rows {mem : ByteArray} {pa n : Nat} (h : Snapshot mem pa n)
    (pb i : Nat) (hn : n ≤ 8) (hpa : pa+32*n ≤ 8192) :
    Snapshot (rowsCarry mem pa pb n i) pa n := by
  induction i with
  | zero => exact h
  | succ i ih => exact ih.row pb i hn hpa

end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand
