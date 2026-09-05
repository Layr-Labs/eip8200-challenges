import Challenge.Ripemd160.Submission.H39Memo.PatternFactsWords

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternFacts

open EvmSemantics EvmSemantics.EVM

/-- Exact size, all complete words, and the optional zero-padded tail suffice. -/
theorem eq_of_prefix_tail (bytes : ByteArray) (p : Fin 14)
    (hsize : bytes.size = (target p).size)
    (hprefix : ∀ k : Fin 31, k.val < (target p).size / 32 →
      MachineState.readWord bytes (32 * k.val) = prefixWord k)
    (htail : (target p).size % 32 ≠ 0 →
      MachineState.readWord bytes (32 * ((target p).size / 32)) = tailWord p) :
    bytes = target p := by
  apply Logic.byteArray_eq_of_readWord_cover bytes (target p) hsize
  intro k hk
  have hlimit := target_size_le p
  by_cases hfull : k < (target p).size / 32
  · have hk31 : k < 31 := by omega
    exact (hprefix ⟨k, hk31⟩ hfull).trans
      (prefix_eq p ⟨k, hk31⟩ (by
        change 32 * (k + 1) ≤ (target p).size
        omega)).symm
  · have hlast : k = (target p).size / 32 := by omega
    have hpartial : (target p).size % 32 ≠ 0 := by omega
    subst k
    exact (htail hpartial).trans (tail_eq p hpartial).symm

end Challenge.Ripemd160.Submission.H39Memo.PatternFacts
