import Challenge.Modexp.Submission.Proofs.Fast.CarryResult
import Challenge.Modexp.Submission.Proofs.Fast.CarryRows
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

theorem readonlyCache_rowsCarry {mem : ByteArray} {n pa pb i : Nat}
    {tl inv m0 : UInt256} (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (hn : n ≤ 32) :
    CiosReadonly.ReadonlyCache (CarryRowModel.rowsCarry mem pa pb n i) n tl inv m0 :=
  hc.of_preserved
    (CarryRowModel.readWord_rowsCarry mem pa pb n 9376 hn (Or.inr (by decide)) i)
    (CarryRowModel.readWord_rowsCarry mem pa pb n (32*n-32) hn (Or.inl (by omega)) i)

theorem extraCache_rowsCarry {mem : ByteArray} {n pa pb i : Nat}
    {m96 m64 m32 : UInt256} (hc : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hn : n ≤ 32) :
    CiosReadonlyExtra.ExtraCache (CarryRowModel.rowsCarry mem pa pb n i) m96 m64 m32 :=
  hc.of_preserved
    (CarryRowModel.readWord_rowsCarry mem pa pb n 96 hn (Or.inl (by decide)) i)
    (CarryRowModel.readWord_rowsCarry mem pa pb n 64 hn (Or.inl (by decide)) i)
    (CarryRowModel.readWord_rowsCarry mem pa pb n 32 hn (Or.inl (by decide)) i)

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CarryRowGas CiosCachedMidMemory
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult

opaque inverse_rowsCarry (mem : ByteArray) (pa pb n i : Nat)
    (hn : n ≤ 32) (hminv : inverseInvariant mem n) :
    inverseInvariant (rowsCarry mem pa pb n i) n := by
  unfold inverseInvariant at *
  rw [readWord_rowsCarry mem pa pb n (32*n-32) hn (Or.inl (by omega)) i,
    readWord_rowsCarry mem pa pb n 9376 hn (Or.inr (by decide)) i]
  exact hminv

theorem readWord_selected_preserved (s : State) (memory : ByteArray)
    (pa pb n i addr : Nat) (hn : n ≤ 32)
    (haddr : addr+32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (selectedRows (mpZeroed s memory n) pa pb n i) addr =
      MachineState.readWord memory addr := by
  rw [selectedRows_readWord_outside _ pa pb n i addr hn haddr,
    readWord_mpZeroed s memory n addr hn haddr]

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
