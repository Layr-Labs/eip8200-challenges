import Challenge.Modexp.Submission.Proofs.Fast.CarryRowModel
import Challenge.Modexp.Submission.Proofs.Fast.SquareInitMemory

set_option warningAsError true
set_option maxHeartbeats 300000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryControl
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro CarryRowModel SquareInit

structure Control (mem : ByteArray) : Prop where
  zero : MachineState.readWord mem 8928 = UInt256.ofNat 0
  route : MachineState.readWord mem 9280 = UInt256.ofNat 4169

theorem read_l1 (mem : ByteArray) (bi : UInt256) (pa n addr : Nat) (hn : n ≤ 8)
    (hd : addr+32 ≤ 8256 ∨ 8512 ≤ addr) :
    ∀ j, MachineState.readWord (l1Step mem bi pa n j).memory addr = MachineState.readWord mem addr := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [l1Step]
    change MachineState.readWord (storeWord _ _ _) addr = _
    rw [read_storeWord_outside _ _ _ _ (by omega), ih]

theorem read_l2 (mem : ByteArray) (mu c0 : UInt256) (n addr : Nat) (hn : n ≤ 8)
    (hd : addr+32 ≤ 8256 ∨ 8512 ≤ addr) :
    ∀ j, MachineState.readWord (l2Step mem mu c0 n j).memory addr = MachineState.readWord mem addr := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [l2Step]
    change MachineState.readWord (storeWord _ _ _) addr = _
    rw [read_storeWord_outside _ _ _ _ (by omega), ih]

theorem read_mid (mem : ByteArray) (c : UInt256) (addr : Nat) (hd : 8512 ≤ addr) :
    MachineState.readWord (midMem1 mem c) addr = MachineState.readWord mem addr :=
  read_storeWord_outside _ _ _ _ (Or.inr (by omega))

theorem read_tail (mem : ByteArray) (c f : UInt256) (addr : Nat) (hd : 8512 ≤ addr) :
    MachineState.readWord (tailCarry mem c f) addr = MachineState.readWord mem addr := by
  change MachineState.readWord (storeWord (storeWord mem 8256 _) 8224 _) addr = _
  rw [read_storeWord_outside _ _ _ _ (Or.inr (by omega)),
    read_storeWord_outside _ _ _ _ (Or.inr (by omega))]

theorem read_rowL2 (mem : ByteArray) (pa pb n i addr : Nat) (hn : n ≤ 8) (hd : 8512 ≤ addr) :
    MachineState.readWord (rowL2Carry mem pa pb n i).memory addr = MachineState.readWord mem addr := by
  rw [rowL2Carry, read_l2 _ _ _ _ _ hn (Or.inr hd), read_mid _ _ _ hd]
  exact read_l1 _ _ _ _ _ hn (Or.inr hd) _

theorem Control.row {mem : ByteArray} (hc : Control mem) (pa pb n i : Nat) (hn : n ≤ 8) :
    Control (rowCarry mem pa pb n i) := by
  constructor
  · rw [rowCarry, read_tail _ _ _ _ (by decide), read_rowL2 _ _ _ _ _ _ hn (by decide)]
    exact hc.zero
  · rw [rowCarry, read_tail _ _ _ _ (by decide), read_rowL2 _ _ _ _ _ _ hn (by decide)]
    exact hc.route

theorem Control.rows {mem : ByteArray} (hc : Control mem) (pa pb n : Nat) (hn : n ≤ 8) :
    ∀ i, Control (rowsCarry mem pa pb n i) := by
  intro i
  induction i with
  | zero => exact hc
  | succ i ih => exact ih.row pa pb n i hn

theorem Control.zeroed {mem : ByteArray} (hc : Control mem) (s : State) (n : Nat) (hn : n ≤ 8) :
    Control (mpZeroed s mem n) := by
  constructor
  · rw [mpZeroed_readWord_outside _ _ _ _ (Or.inr (by omega))]; exact hc.zero
  · rw [mpZeroed_readWord_outside _ _ _ _ (Or.inr (by omega))]; exact hc.route

end Challenge.Modexp.Submission.Proofs.Fast.CarryControl
