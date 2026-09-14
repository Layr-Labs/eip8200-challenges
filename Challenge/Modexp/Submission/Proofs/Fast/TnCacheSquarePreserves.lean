import Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPreserves

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquarePreserves
open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel CiosCachedMidMemory
open TnCacheRowModel TnCacheSquareModel TnCacheRowPreserves

theorem sqL1_cached {mem : ByteArray} {n : Nat} {tl inv m0 m96 m64 m32 : UInt256}
    (h : Cached mem 2368 n tl inv m0 m96 m64 m32) (i : Nat) (tb : UInt256)
    (hi : i < n) (hn : n ≤ 8) :
    Cached (sqL1 mem n i tb).memory 2368 n tl inv m0 m96 m64 m32 := by
  refine ⟨h.readonly.of_preserved
      (readWord_sqL1 mem n i 2720 tb hi (Or.inr (by omega)))
      (readWord_sqL1 mem n i (32*n-32) tb hi (Or.inl (by omega))),
    h.extra.of_preserved
      (readWord_sqL1 mem n i 96 tb hi (Or.inl (by decide)))
      (readWord_sqL1 mem n i 64 tb hi (Or.inl (by decide)))
      (readWord_sqL1 mem n i 32 tb hi (Or.inl (by decide))), ?_, ?_⟩
  · unfold inverseInvariant
    rw [readWord_sqL1 mem n i (32*n-32) tb hi (Or.inl (by omega)),
      readWord_sqL1 mem n i 2720 tb hi (Or.inr (by omega))]
    exact h.inverse
  · intro j _; rfl

theorem read_squareRow (z : CacheState) (n i addr : Nat) (hi : i < n) (hn : n ≤ 8)
    (hout : addr+32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (squareRow z n i).memory addr = MachineState.readWord z.memory addr := by
  unfold squareRow
  rw [read_fromL1 _ _ n addr hn hout]
  exact readWord_sqL1 z.memory n i addr (sqTb z.memory n i) hi (by omega)

theorem read_squareRows (z : CacheState) (n addr : Nat) (hn : n ≤ 8)
    (hout : addr+32 ≤ 2048 ∨ 2368 ≤ addr) :
    ∀ i, i ≤ n → MachineState.readWord (squareRows z n i).memory addr = MachineState.readWord z.memory addr
  | 0, _ => rfl
  | i+1, hi => by
      rw [squareRows, read_squareRow _ n i addr (by omega) hn hout,
        read_squareRows z n addr hn hout i (by omega)]

theorem cached_squareRows {z : CacheState} {n : Nat} {tl inv m0 m96 m64 m32 : UInt256}
    (h : Cached z.memory 2368 n tl inv m0 m96 m64 m32) (hn : n ≤ 8) (i : Nat) (hi : i ≤ n) :
    Cached (squareRows z n i).memory 2368 n tl inv m0 m96 m64 m32 := by
  refine ⟨h.readonly.of_preserved
      (read_squareRows z n 2720 hn (Or.inr (by decide)) i hi)
      (read_squareRows z n (32*n-32) hn (Or.inl (by omega)) i hi),
    h.extra.of_preserved
      (read_squareRows z n 96 hn (Or.inl (by decide)) i hi)
      (read_squareRows z n 64 hn (Or.inl (by decide)) i hi)
      (read_squareRows z n 32 hn (Or.inl (by decide)) i hi), ?_, ?_⟩
  · unfold inverseInvariant
    rw [read_squareRows z n (32*n-32) hn (Or.inl (by omega)) i hi,
      read_squareRows z n 2720 hn (Or.inr (by decide)) i hi]
    exact h.inverse
  · intro j _; rfl

#print axioms sqL1_cached
#print axioms cached_squareRows
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquarePreserves
