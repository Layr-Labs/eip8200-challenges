import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareModel
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheExtraTrace
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandSnapshot

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPreserves
open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosReadonly CiosCachedMidMemory
open TnCacheMemory TnCacheRowModel TnCacheSquareModel StagedOperand

theorem read_fromL1 (q : MacState) (tn : UInt256) (n addr : Nat) (hn : n ≤ 8)
    (hout : addr+32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (fromL1 q tn n).memory addr = MachineState.readWord q.memory addr := by
  change MachineState.readWord (put _ _ 2112) addr = _
  rw [read_put_outside _ _ 2112 addr (by omega)]
  rcases hout with hlow | hhigh
  · exact readWord_l2Step q.memory (rowMu q.memory n) (rowC0 q.memory n) n addr (n-1)
      hn (Or.inl hlow)
  · exact read_l2_high q.memory (rowMu q.memory n) (rowC0 q.memory n) n addr (n-1) hn hhigh

theorem read_row (z : CacheState) (pa pb n i addr : Nat) (hn : n ≤ 8)
    (hout : addr+32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (row z pa pb n i).memory addr = MachineState.readWord z.memory addr := by
  change MachineState.readWord
    (fromL1 (l1Step z.memory (rowBi z.memory pb n i) pa n n) z.tn n).memory addr = _
  rw [read_fromL1 _ _ n addr hn hout]
  rcases hout with hlow | hhigh
  · exact readWord_l1Step z.memory (rowBi z.memory pb n i) pa n addr n hn (Or.inl hlow)
  · exact read_l1_high z.memory (rowBi z.memory pb n i) pa n addr n hn hhigh

theorem read_rows (z : CacheState) (pa pb n addr : Nat) (hn : n ≤ 8)
    (hout : addr+32 ≤ 2048 ∨ 2368 ≤ addr) (i : Nat) :
    MachineState.readWord (rows z pa pb n i).memory addr = MachineState.readWord z.memory addr := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [rows, read_row _ pa pb n i addr hn hout, ih]

structure Cached (mem : ByteArray) (pa n : Nat) (tl inv m0 m96 m64 m32 : UInt256) : Prop where
  readonly : ReadonlyCache mem n tl inv m0
  extra : TnCacheExtraTrace.ExtraCache mem m96 m64 m32
  inverse : inverseInvariant mem n
  snapshot : Snapshot mem pa n

theorem Cached.row {z : CacheState} {pa n : Nat} {tl inv m0 m96 m64 m32 : UInt256}
    (h : Cached z.memory pa n tl inv m0 m96 m64 m32) (pb i : Nat)
    (hn : n ≤ 8) (hpa : pa+32*n ≤ 2048 ∨ pa = 2368) :
    Cached (TnCacheRowModel.row z pa pb n i).memory pa n tl inv m0 m96 m64 m32 := by
  refine ⟨h.readonly.of_preserved
      (read_row z pa pb n i 2720 hn (Or.inr (by decide)))
      (read_row z pa pb n i (32*n-32) hn (Or.inl (by omega))),
    h.extra.of_preserved
      (read_row z pa pb n i 96 hn (Or.inl (by decide)))
      (read_row z pa pb n i 64 hn (Or.inl (by decide)))
      (read_row z pa pb n i 32 hn (Or.inl (by decide))), ?_, ?_⟩
  · unfold inverseInvariant
    rw [read_row z pa pb n i (32*n-32) hn (Or.inl (by omega)),
      read_row z pa pb n i 2720 hn (Or.inr (by decide))]
    exact h.inverse
  · rcases hpa with hfit | rfl
    · intro j hj
      rw [read_row z pa pb n i (2368+32*j) hn (Or.inr (by omega)),
        read_row z pa pb n i (pa+32*j) hn (Or.inl (by omega))]
      exact h.snapshot j hj
    · intro j _; rfl

theorem Cached.rows {z : CacheState} {pa n : Nat} {tl inv m0 m96 m64 m32 : UInt256}
    (h : Cached z.memory pa n tl inv m0 m96 m64 m32) (pb i : Nat)
    (hn : n ≤ 8) (hpa : pa+32*n ≤ 2048 ∨ pa = 2368) :
    Cached (TnCacheRowModel.rows z pa pb n i).memory pa n tl inv m0 m96 m64 m32 := by
  induction i with
  | zero => exact h
  | succ i ih => exact ih.row pb i hn hpa

#print axioms Cached.row
#print axioms Cached.rows
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPreserves
