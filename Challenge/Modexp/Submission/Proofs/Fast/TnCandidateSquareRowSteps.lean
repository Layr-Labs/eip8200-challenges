import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateL1Jumps
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquarePreserves
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPointers

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareRowSteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareModel
open TnCacheRowModel TnCacheRowPreserves TnCacheRowPointers TnCacheSquarePreserves
open TnCandidateReductionSteps

def sqEnt (n i : Nat) : Nat := 3740+37*(8-n+i)

theorem sqEnt_suffix (n i : Nat) (hn : n ≤ 8) (hi : i < n) :
    sqEnt n i = 3999-37*(n-1-i) := by unfold sqEnt; omega

theorem sqEnt_next (n i : Nat) : sqEnt n i + 37 = sqEnt n (i+1) := by
  unfold sqEnt; omega

def result (z : CacheState) (n i : Nat) (aprev : UInt256) : CacheState :=
  TnCacheSquareModel.fromL1 (sqL1 z.memory n i (UInt256.sgt (UInt256.ofNat 0) aprev)) z.tn n

def rowState (s : State) (z : CacheState) (n i : Nat) (aprev : UInt256)
    (tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := z.memory}
    (if i < n then UInt256.ofNat 4471 else UInt256.ofNat 4292)
    (TnCacheFrameOps.frame (pointer 2368 n i) (UInt256.ofNat 4471) (UInt256.ofNat 2336)
      (UInt256.ofNat (sqEnt n i)) z.tn (UInt256.ofNat (l2PC n)) inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aprev :: dst :: ret :: rest))

/-- One complete square row, including its shrinking first loop, full reduction,
and real next-row branch, with arbitrary incoming cached carry and previous limb. -/
noncomputable def step (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (n i : Nat) (hn : n = 4 ∨ n = 8) (hi : i < n)
    (aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hc : Cached z.memory 2368 n tl inv m0 m96 m64 m32) :
    GasSteps (rowState s z n i aprev tl inv m0 m96 m64 m32 dst ret rest)
      (rowState s (result z n i aprev) n (i+1) (sqX z.memory n i)
        tl inv m0 m96 m64 m32 dst ret rest) := by
  let tb := UInt256.sgt (UInt256.ofNat 0) aprev
  let q0 := sqPro z.memory n i tb
  let b2 := sqB2 (sqX z.memory n i) tb
  let q1 := sqL1 z.memory n i tb
  let tail := m0 :: tl :: m96 :: m64 :: m32 :: sqX z.memory n i :: dst :: ret :: rest
  have hn8 : n ≤ 8 := by omega
  have he := sqEnt_suffix n i hn8 hi
  have hj : Decode.isValidJumpDest TnCandidate.bytecode (sqEnt n i) = true := by
    rw [he]; exact TnCandidateL1Jumps.entry_jump (n-1-i) (by omega)
  have hhead : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4471).toNat = true := by
    change Decode.isValidJumpDest s.executionEnv.code 4471 = true
    rw [env.code]; exact TnCandidateL1Jumps.square_jump
  have g0 := TnCandidateSquareSteps.prologue_steps s z.memory z.tn n i (sqEnt n i)
    inv m0 tl m96 m64 m32 aprev (dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) env.running env.code env.forkEq env.noPrecompile
    hact hi hn8 hj (by unfold sqEnt; omega)
  have g1 := TnCandidateL1Steps.suffix_steps s env q0 b2 2368 n (i+1) (n-1-i) (by omega)
    (pointer 2368 n i) (UInt256.ofNat 4471) (UInt256.ofNat 2336)
    (UInt256.ofNat (sqEnt n i+37)) z.tn (UInt256.ofNat (l2PC n)) inv tail
    (by simp only [tail, List.length_cons]; omega) hact hn8 (by omega)
    (Or.inr rfl) (by intro j _; rfl)
  rw [← he] at g1
  have g01 := g0.trans g1
  have hc1 := sqL1_cached hc i tb hi hn8
  have g2 := reduction_steps s env q1 b2 z.tn n hn
    (pointer 2368 n i) (UInt256.ofNat 4471) (UInt256.ofNat 2336)
    (UInt256.ofNat (sqEnt n i+37)) tl inv m0 (sqX z.memory n i) m96 m64 m32 dst ret rest
    hcap hact hc1.readonly hc1.extra hc1.inverse hhead
  have both := g01.trans g2
  have hcond := pointer_condition 2368 n i (by decide) (by omega) hi
  rw [pointer_succ] at hcond
  rw [pointer_succ] at both
  simp only [hcond, l2_end n hn, sqEnt_next, Nat.reduceAdd] at both
  simpa only [rowState, if_pos hi, TnCandidateSquareSteps.outState,
    TnCandidateSquareSteps.l1Q, result, sqL1, q0, q1, b2, tb, tail,
    pointer, Nat.reduceSub] using both

#print axioms step
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareRowSteps
