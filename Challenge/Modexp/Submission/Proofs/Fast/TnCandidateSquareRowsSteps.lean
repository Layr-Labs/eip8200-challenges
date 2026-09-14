import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareRowSteps

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareRowsSteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel
open TnCacheRowModel TnCacheSquareModel TnCacheRowPreserves TnCacheSquarePreserves
open TnCandidateSquareRowSteps

def previous (a0 : UInt256) (mem : ByteArray) (n : Nat) : Nat → UInt256
  | 0 => a0
  | i+1 => sqX mem n i

theorem tb_previous (a0 : UInt256) (z : CacheState) (n i : Nat) (hn : n ≤ 8) (hi : i ≤ n)
    (ha0 : UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0) :
    UInt256.sgt (UInt256.ofNat 0) (previous a0 z.memory n i) =
      sqTb (squareRows z n i).memory n i := by
  cases i with
  | zero => exact ha0
  | succ i =>
      simp only [previous, sqTb, sqX,
        read_squareRows z n (aAddr n i) hn (Or.inr (by unfold aAddr; omega)) (i+1) hi]

theorem previous_next (a0 : UInt256) (z : CacheState) (n i : Nat) (hn : n ≤ 8) (hi : i ≤ n) :
    sqX (squareRows z n i).memory n i = previous a0 z.memory n (i+1) := by
  unfold previous sqX
  exact read_squareRows z n (aAddr n i) hn (Or.inr (by unfold aAddr; omega)) i hi

/-- Every square row computes the cache-aware square model, while the stack
remembers the preceding operand limb for the signed carry bit. -/
noncomputable def rows_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (n : Nat) (hn : n = 4 ∨ n = 8)
    (a0 tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hc : Cached z.memory 2368 n tl inv m0 m96 m64 m32)
    (ha0 : UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0) :
    ∀ i, i ≤ n → GasSteps (rowState s z n 0 a0 tl inv m0 m96 m64 m32 dst ret rest)
      (rowState s (squareRows z n i) n i (previous a0 z.memory n i)
        tl inv m0 m96 m64 m32 dst ret rest)
  | 0, _ => .refl _
  | i+1, hi => by
      have prev := rows_steps s env z n hn a0 tl inv m0 m96 m64 m32 dst ret rest
        hcap hact hc ha0 i (by omega)
      have next := TnCandidateSquareRowSteps.step s env (squareRows z n i) n i hn (by omega)
        (previous a0 z.memory n i) tl inv m0 m96 m64 m32 dst ret rest hcap hact
        (cached_squareRows hc (by omega) i (by omega))
      have heq : result (squareRows z n i) n i (previous a0 z.memory n i) =
          squareRow (squareRows z n i) n i := by
        unfold result squareRow
        rw [tb_previous a0 z n i (by omega) (by omega) ha0]
      rw [heq, previous_next a0 z n i (by omega) (by omega)] at next
      exact prev.trans next

/-- Continue after any already-computed square prefix. This connects the
specialized first row to the shared remaining rows. -/
noncomputable def rows_from (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (n start : Nat) (hn : n = 4 ∨ n = 8)
    (a0 tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hc : Cached z.memory 2368 n tl inv m0 m96 m64 m32)
    (ha0 : UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0) :
    ∀ count, start + count ≤ n →
      GasSteps
        (rowState s (squareRows z n start) n start (previous a0 z.memory n start)
          tl inv m0 m96 m64 m32 dst ret rest)
        (rowState s (squareRows z n (start + count)) n (start + count)
          (previous a0 z.memory n (start + count)) tl inv m0 m96 m64 m32 dst ret rest)
  | 0, _ => .refl _
  | count+1, hi => by
      have prev := rows_from s env z n start hn a0 tl inv m0 m96 m64 m32 dst ret rest
        hcap hact hc ha0 count (by omega)
      have next := TnCandidateSquareRowSteps.step s env (squareRows z n (start+count))
        n (start+count) hn (by omega) (previous a0 z.memory n (start+count))
        tl inv m0 m96 m64 m32 dst ret rest hcap hact
        (cached_squareRows hc (by omega) (start+count) (by omega))
      have heq : result (squareRows z n (start+count)) n (start+count)
          (previous a0 z.memory n (start+count)) =
          squareRow (squareRows z n (start+count)) n (start+count) := by
        unfold result squareRow
        rw [tb_previous a0 z n (start+count) (by omega) (by omega) ha0]
      rw [heq, previous_next a0 z n (start+count) (by omega) (by omega)] at next
      exact prev.trans next

#print axioms rows_from
#print axioms tb_previous
#print axioms rows_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareRowsSteps
