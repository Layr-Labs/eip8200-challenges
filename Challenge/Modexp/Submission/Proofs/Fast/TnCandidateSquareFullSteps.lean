import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareRowsSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateExitBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareFullSteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCachedMacCore
open TnCacheMemory TnCacheRowModel TnCacheSquareModel TnCacheRowPreserves TnCacheRowPointers
open TnCandidateSquareRowSteps TnCandidateSquareRowsSteps TnCandidateReductionSteps

def exitState (s : State) (mem : ByteArray) (tn : UInt256) (n : Nat)
    (aprev tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 4362)
    (TnCacheFrameOps.frame (UInt256.ofNat 2336) (UInt256.ofNat 4471) (UInt256.ofNat 2336)
      (UInt256.ofNat 4036) tn (UInt256.ofNat (l2PC n)) inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aprev :: dst :: ret :: rest))

noncomputable def finish_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (n : Nat) (hn : n ≤ 8)
    (aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (rowState s z n n aprev tl inv m0 m96 m64 m32 dst ret rest)
      (exitState s (lift z.memory z.tn) z.tn n aprev tl inv m0 m96 m64 m32 dst ret rest) := by
  let tail := m0 :: tl :: m96 :: m64 :: m32 :: aprev :: dst :: ret :: rest
  let st : State := {s with memory := z.memory}
  let aft : State := {s with memory := lift z.memory z.tn}
  let stack := TnCacheFrameOps.frame (pointer 2368 n n) (UInt256.ofNat 4471) (UInt256.ofNat 2336)
    (UInt256.ofNat (sqEnt n n)) z.tn (UInt256.ofNat (l2PC n)) inv tail
  have htail : tail.length ≤ 1006 := by simp only [tail, List.length_cons]; omega
  have hj : Decode.isValidJumpDest aft.executionEnv.code 4362 = true := by
    rw [show aft.executionEnv.code = TnCandidateArtifact.submissionArtifact.code from env.code]
    exact TnCandidateArtifact.isValidJumpDest_index 3302 (by rfl)
  have hf := TnCacheFrameOps.run_flush 4292 st (pointer 2368 n n) (UInt256.ofNat 4471)
    (UInt256.ofNat 2336) (UInt256.ofNat (sqEnt n n)) z.tn (UInt256.ofNat (l2PC n)) inv
    tail htail hact
  have g0 := TnCandidateBlocks.flush.steps
    (s := framed st (UInt256.ofNat 4292) stack) (env.transfer rfl rfl) rfl hf
  have hg := TnCacheExitTrace.run_square_guard aft 4297 (pointer 2368 n n)
    (UInt256.ofNat 2336) (UInt256.ofNat (sqEnt n n)) z.tn (UInt256.ofNat (l2PC n)) inv
    tail htail hj
  have g1 := TnCandidateExitBlocks.guard.steps
    (s := framed aft (UInt256.ofNat 4297) stack) (env.transfer rfl rfl) rfl hg
  have hp := pointer_end 2368 n (by decide) (by omega)
  have he : sqEnt n n = 4036 := by unfold sqEnt; omega
  simpa only [rowState, exitState, if_neg (Nat.lt_irrefl n), st, aft, stack, tail,
    hp, he, Nat.reduceSub] using g0.trans g1

/-- All square rows, materialization of the cached carry, and the square exit
branch compute the existing square model. Entry and exponent-loop control are external. -/
noncomputable def square_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (n : Nat) (hn : n = 4 ∨ n = 8)
    (a0 tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hc : Cached z.memory 2368 n tl inv m0 m96 m64 m32)
    (ha0 : UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0) :
    GasSteps (rowState s z n 0 a0 tl inv m0 m96 m64 m32 dst ret rest)
      (exitState s (SquareResult.sqRowsCarry (lift z.memory z.tn) n n) (squareRows z n n).tn n
        (previous a0 z.memory n n) tl inv m0 m96 m64 m32 dst ret rest) := by
  have hr := rows_steps s env z n hn a0 tl inv m0 m96 m64 m32 dst ret rest hcap hact hc ha0 n le_rfl
  have hf := finish_steps s env (squareRows z n n) n (by omega)
    (previous a0 z.memory n n) tl inv m0 m96 m64 m32 dst ret rest hcap hact
  have hlift := squareRows_lift z n n le_rfl (by omega)
  have both := hr.trans hf
  rw [← hlift] at both
  exact both

#print axioms finish_steps
#print axioms square_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareFullSteps
