import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareTailSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFinishSteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCachedMacCore
open TnCacheMemory TnCacheRowModel TnCacheSquareModel TnCacheRowPreserves TnCacheRowPointers
open TnM128SquareRowSteps TnM128SquareTailSteps TnM128ReductionSteps

def exitState (s : State) (mem : ByteArray) (tn : UInt256) (_n : Nat)
    (aprev tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 4208)
    (TnCacheFrameOps.frame (UInt256.ofNat 2336) (UInt256.ofNat 4268) (UInt256.ofNat 2336)
      (UInt256.ofNat 3868) tn (MachineState.readWord mem 128) inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aprev :: dst :: ret :: rest))

noncomputable def finish_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (n : Nat) (hn : n ≤ 8)
    (aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (rowState s z n n aprev tl inv m0 m96 m64 m32 dst ret rest)
      (exitState s (lift z.memory z.tn) z.tn n aprev tl inv m0 m96 m64 m32 dst ret rest) := by
  let tail := m0 :: tl :: m96 :: m64 :: m32 :: aprev :: dst :: ret :: rest
  let st : State := {s with memory := z.memory}
  let aft : State := {s with memory := lift z.memory z.tn}
  let stack := TnCacheFrameOps.frame (pointer 2368 n n) (UInt256.ofNat 4268) (UInt256.ofNat 2336)
    (UInt256.ofNat (sqEnt n n)) z.tn (MachineState.readWord z.memory 128) inv tail
  have htail : tail.length ≤ 1006 := by simp only [tail, List.length_cons]; omega
  have hj : Decode.isValidJumpDest aft.executionEnv.code 4208 = true := by
    rw [show aft.executionEnv.code = TnM128CandidateArtifact.submissionArtifact.code from env.code]
    exact TnM128CandidateArtifact.isValidJumpDest_index 3353 (by rfl)
  have hf := TnCacheFrameOps.run_flush 4138 st (pointer 2368 n n) (UInt256.ofNat 4268)
    (UInt256.ofNat 2336) (UInt256.ofNat (sqEnt n n)) z.tn (MachineState.readWord z.memory 128) inv
    tail htail hact
  have g0 := TnM128CandidateBlocks.flush.steps
    (s := framed st (UInt256.ofNat 4138) stack) (env.transfer rfl rfl) rfl hf
  have hg := TnCacheExitTrace.run_square_guard aft 4143 (pointer 2368 n n)
    (UInt256.ofNat 2336) (UInt256.ofNat (sqEnt n n)) z.tn (MachineState.readWord z.memory 128) inv
    tail htail hj
  have g1 := TnM128L1Blocks.guard.steps
    (s := framed aft (UInt256.ofNat 4143) stack) (env.transfer rfl rfl) rfl hg
  have hp := pointer_end 2368 n (by decide) (by omega)
  have he : sqEnt n n = 3868 := by unfold sqEnt; omega
  simpa only [rowState, exitState, if_neg (Nat.lt_irrefl n), st, aft, stack, tail,
    hp, he, Nat.reduceSub,
    read_lift_outside z.memory z.tn 128 (Or.inl (by decide))] using g0.trans g1

#print axioms finish_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFinishSteps
