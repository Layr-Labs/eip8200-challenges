import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareRowSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFirstModel

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareTailSteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel SquareResult CiosCachedMidMemory
open TnCacheMemory TnCacheRowModel TnCacheSquareModel TnCacheRowPreserves TnCacheSquarePreserves
open TnM128SquareRowSteps

/-- The previous operand word retained by the square-row frame. -/
def previous (mem : ByteArray) (n : Nat) : Nat → UInt256
  | 0 => UInt256.ofNat 0
  | i+1 => sqX mem n i

theorem tb_previous (mem : ByteArray) (n i : Nat) :
    UInt256.sgt (UInt256.ofNat 0) (previous mem n i) = sqTb mem n i := by
  cases i with
  | zero => rfl
  | succ i => rfl

def run (z : CacheState) (n start : Nat) : Nat → CacheState
  | 0 => z
  | k+1 => squareRow (run z n start k) n (start+k)

theorem row_cached {z : CacheState} {n : Nat} {tl inv m0 m96 m64 m32 : UInt256}
    (h : Cached z.memory 2368 n tl inv m0 m96 m64 m32) (i : Nat) (hi : i < n) (hn : n ≤ 8) :
    Cached (squareRow z n i).memory 2368 n tl inv m0 m96 m64 m32 := by
  refine ⟨h.readonly.of_preserved
      (read_squareRow z n i 2720 hi hn (Or.inr (by decide)))
      (read_squareRow z n i (32*n-32) hi hn (Or.inl (by omega))),
    h.extra.of_preserved
      (read_squareRow z n i 96 hi hn (Or.inl (by decide)))
      (read_squareRow z n i 64 hi hn (Or.inl (by decide)))
      (read_squareRow z n i 32 hi hn (Or.inl (by decide))), ?_, fun _ _ => rfl⟩
  unfold inverseInvariant
  rw [read_squareRow z n i (32*n-32) hi hn (Or.inl (by omega)),
    read_squareRow z n i 2720 hi hn (Or.inr (by decide))]
  exact h.inverse

theorem run_cached {z : CacheState} {n : Nat} {tl inv m0 m96 m64 m32 : UInt256}
    (h : Cached z.memory 2368 n tl inv m0 m96 m64 m32) (hn : n ≤ 8) (start : Nat) :
    ∀ k, start+k ≤ n → Cached (run z n start k).memory 2368 n tl inv m0 m96 m64 m32
  | 0, _ => h
  | k+1, hk => row_cached (run_cached h hn start k (by omega)) (start+k) (by omega) hn

theorem run_read (z : CacheState) (n start addr : Nat) (hn : n ≤ 8)
    (hout : addr+32 ≤ 2048 ∨ 2368 ≤ addr) :
    ∀ k, start+k ≤ n →
      MachineState.readWord (run z n start k).memory addr = MachineState.readWord z.memory addr
  | 0, _ => rfl
  | k+1, hk => by
      rw [run, read_squareRow _ n (start+k) addr (by omega) hn hout,
        run_read z n start addr hn hout k (by omega)]

theorem run_lift (z : CacheState) (mem : ByteArray) (n start : Nat) (hn : n ≤ 8)
    (h : lift z.memory z.tn = sqRowsCarry mem n start) :
    ∀ k, start+k ≤ n →
      lift (run z n start k).memory (run z n start k).tn = sqRowsCarry mem n (start+k)
  | 0, _ => h
  | k+1, hk => by
      rw [run, ← squareRow_lift _ n (start+k) (by omega) hn,
        run_lift z mem n start hn h k (by omega)]
      rfl

def state (s : State) (z : CacheState) (n i : Nat)
    (tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256) : State :=
  rowState s z n i (previous z.memory n i) tl inv m0 m96 m64 m32 dst ret rest

noncomputable def step (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (n i : Nat) (hn : n = 8) (hi : i < n)
    (tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hc : Cached z.memory 2368 n tl inv m0 m96 m64 m32) :
    GasSteps (state s z n i tl inv m0 m96 m64 m32 dst ret rest)
      (state s (squareRow z n i) n (i+1) tl inv m0 m96 m64 m32 dst ret rest) := by
  have g := TnM128SquareRowSteps.step s env z n i hn hi (previous z.memory n i)
    tl inv m0 m96 m64 m32 dst ret rest hcap hact hc
  have he : result z n i (previous z.memory n i) = squareRow z n i := by
    unfold result squareRow
    rw [tb_previous]
  rw [he] at g
  have hp : previous (squareRow z n i).memory n (i+1) = sqX z.memory n i := by
    unfold previous sqX
    exact read_squareRow z n i (aAddr n i) hi (by omega) (Or.inr (by unfold aAddr; omega))
  simpa only [state, hp] using g

/-- Continue all remaining rows from an arbitrary correctly framed prefix. -/
noncomputable def steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (n start : Nat) (hn : n = 8)
    (tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hc : Cached z.memory 2368 n tl inv m0 m96 m64 m32) :
    ∀ k, start+k ≤ n →
      GasSteps (state s z n start tl inv m0 m96 m64 m32 dst ret rest)
        (state s (run z n start k) n (start+k) tl inv m0 m96 m64 m32 dst ret rest)
  | 0, _ => .refl _
  | k+1, hk => by
      exact (steps s env z n start hn tl inv m0 m96 m64 m32 dst ret rest
        hcap hact hc k (by omega)).trans
        (step s env (run z n start k) n (start+k) hn (by omega)
          tl inv m0 m96 m64 m32 dst ret rest hcap hact
          (run_cached hc (by omega) start k (by omega)))

#print axioms run_lift
#print axioms steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareTailSteps
