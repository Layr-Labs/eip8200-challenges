/- Carry preservation and caller integration using the scratch-memory model
   adapted from delordemm1 submission 173ec87d-b01c-4a3b-b36a-e0a008eb4d72. -/
import Challenge.Modexp.Submission.Proofs.Fast.CarryResult
import Challenge.Modexp.Submission.Proofs.Fast.CiosOperandCache
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponents

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorInvariants
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryRowModel CarryScratchAgreement CiosCachedMidMemory
open CiosCached CiosReadonly CiosCachedMacCore

theorem inverse_rowsCarry (mem : ByteArray) (pa pb n i : Nat)
    (hn : n ≤ 32) (hminv : inverseInvariant mem n) :
    inverseInvariant (rowsCarry mem pa pb n i) n := by
  unfold inverseInvariant at *
  rw [readWord_rowsCarry mem pa pb n (32*n-32) hn (Or.inl (by omega)) i,
    readWord_rowsCarry mem pa pb n 9376 hn (Or.inr (by decide)) i]
  exact hminv

theorem readonly_rows {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (pa pb i : Nat) :
    ReadonlyCache (rowsCarry mem pa pb n i) n tl inv m0 :=
  h.of_preserved
    (readWord_rowsCarry mem pa pb n 9376 hn (Or.inr (by decide)) i)
    (readWord_rowsCarry mem pa pb n (32*n-32) hn (Or.inl (by omega)) i)

theorem operand_rows {mem : ByteArray} {pa n : Nat}
    {a96 a64 a32 aLast : UInt256}
    (h : CiosOperandCache.OperandCache mem pa n a96 a64 a32 aLast) (pb i : Nat)
    (hn : n ≤ 32) (hfour : 4 ≤ n) (hpa : pa + 32*n ≤ 8192) :
    CiosOperandCache.OperandCache (rowsCarry mem pa pb n i) pa n a96 a64 a32 aLast := by
  apply h.of_preserved
    (fun addr ha => readWord_rowsCarry mem pa pb n addr hn (Or.inl ha) i) hfour hpa

theorem readonly_middle {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (c : UInt256) :
    ReadonlyCache (midMem1 mem c) n tl inv m0 :=
  h.of_preserved
    (readWord_midMem1 mem c 9376 (Or.inr (by decide)))
    (readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)))

theorem inverse_middle (mem : ByteArray) (c : UInt256) (n : Nat)
    (hn : n ≤ 32) (h : inverseInvariant mem n) :
    inverseInvariant (midMem1 mem c) n := by
  unfold inverseInvariant at *
  rw [readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)),
    readWord_midMem1 mem c 9376 (Or.inr (by decide))]
  exact h

theorem readWord_selected_preserved (s : State) (memory : ByteArray)
    (pa pb n i addr : Nat) (hn : n ≤ 32)
    (haddr : addr+32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (CarryResult.selectedRows (mpZeroed s memory n) pa pb n i) addr =
      MachineState.readWord memory addr := by
  rw [CarryResult.selectedRows_readWord_outside _ pa pb n i addr hn haddr,
    readWord_mpZeroed s memory n addr hn haddr]

end Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorInvariants
