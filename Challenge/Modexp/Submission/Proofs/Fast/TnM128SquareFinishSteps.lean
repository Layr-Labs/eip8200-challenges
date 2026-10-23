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

/-- st8/n8g: the square rows leave through the mode test straight to the `n8` block (pc 4207)
with the carry word still in the frame (no flush) and the row pointer at zero. -/
def exitState (s : State) (mem : ByteArray) (tn : UInt256) (_n : Nat)
    (aprev w3 tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 3942)
    (TnCacheFrameOps.frame (UInt256.ofNat 0) (UInt256.ofNat 5297) w3
      (UInt256.ofNat 3643) m32 (MachineState.readWord mem 128) m64
      (m0 :: tl :: m96 :: inv :: tn :: aprev :: dst :: ret :: rest))

noncomputable def finish_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (n : Nat) (hn : n ≤ 8)
    (aprev w3 tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (_hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (rowState s z n n aprev w3 tl inv m0 m96 m64 m32 dst ret rest)
      (exitState s z.memory z.tn n aprev w3 tl inv m0 m96 m64 m32 dst ret rest) := by
  let tail := m0 :: tl :: m96 :: inv :: z.tn :: aprev :: dst :: ret :: rest
  let st : State := {s with memory := z.memory}
  let stack := TnCacheFrameOps.frame (qptr n n) (UInt256.ofNat 5297) w3
    (UInt256.ofNat (sqEnt n n)) m32 (MachineState.readWord z.memory 128) m64 tail
  have htail : tail.length ≤ 1006 := by simp only [tail, List.length_cons]; omega
  have hj : Decode.isValidJumpDest st.executionEnv.code 3942 = true := by
    rw [show st.executionEnv.code = TnM128CandidateArtifact.submissionArtifact.code from env.code]
    exact TnM128CandidateArtifact.isValidJumpDest_index 3095 (by rfl)
  have hg := TnCacheExitTrace.run_square_guard st 3874 (qptr n n)
    w3 (UInt256.ofNat (sqEnt n n)) m32 (MachineState.readWord z.memory 128) m64
    tail htail hj
  have g1 := TnM128L1Blocks.guard.steps
    (s := framed st (UInt256.ofNat 3874) stack) (env.transfer rfl rfl) rfl hg
  have hq : qptr n n = UInt256.ofNat 0 := qptr_end n
  have he : sqEnt n n = 3643 := by unfold sqEnt; omega
  simpa only [rowState, exitState, if_neg (Nat.lt_irrefl n), st, stack, tail, hq, he] using g1

#print axioms finish_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFinishSteps
