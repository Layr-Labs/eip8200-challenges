/- Carry preservation and caller integration using the scratch-memory model
   adapted from delordemm1 submission 173ec87d-b01c-4a3b-b36a-e0a008eb4d72. -/
import Challenge.Modexp.Submission.Proofs.Fast.CarryResult
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowTrace
import Challenge.Modexp.Submission.Proofs.Fast.CiosOperandCache

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryCached
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryRowModel CarryScratchAgreement CiosCachedMidMemory
open CiosCached CiosReadonly CiosCachedMidDefs CiosCachedMacCore

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

theorem run_middle (s : State) (mem : ByteArray) (c bi : UInt256)
    (pa pb n i : Nat) (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middle
      (midState s mem c bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (l2At 4569 s (midMem1 mem c) (overflow mem c) (rowMu mem n) (rowC0 mem n)
      pa pb n i 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hagree := middle_agree mem mem (refl mem) c
  have hmu : rowMu (midMem1 mem c) n = rowMu mem n :=
    (CarryRowModel.rowMu_eq _ _ hagree n).trans (rowMu_mid mem c n hn)
  have hc0 : rowC0 (midMem1 mem c) n = rowC0 mem n :=
    (CarryRowModel.rowC0_eq _ _ hagree n hn32).trans (rowC0_mid mem c n hn hn32)
  have trace := runInstructions_append_some _ _ _ _ _
    (CarryRowTrace.run_middleStore {s with memory := mem} c bi
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
      (l1Target n) (l2Target n) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hact)
    (run_cachedProduct_model {s with memory := midMem1 mem c}
      (overflow mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa)
      (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret n rest hcap hn32 hact
      (readonly_middle hc hn32 c) (inverse_middle mem c n hn32 hminv))
  simpa only [CarryRowPrograms.middle, cacheStack, baseStack, framed, midState, l2At, l2Step,
    hmu, hc0, List.append_assoc, List.cons_append, List.nil_append] using trace

end Challenge.Modexp.Submission.Proofs.Fast.CarryCached
