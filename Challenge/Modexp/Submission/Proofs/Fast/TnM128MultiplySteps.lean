import Challenge.Modexp.Submission.Proofs.Fast.TnM128RowsSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128MultiplySteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCachedMacCore
open TnCacheMemory TnCacheRowModel TnCacheRowPreserves TnCacheRowPointers
open TnM128RowSteps TnM128RowsSteps TnM128ReductionSteps

noncomputable def finish_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (pb n : Nat)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (rowState s z pb n n tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (framed {s with memory := lift z.memory z.tn} (UInt256.ofNat 3991) (dst :: ret :: rest)) := by
  let tail := m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest
  let st : State := {s with memory := z.memory}
  let aft : State := {s with memory := lift z.memory z.tn}
  let stack := TnCacheFrameOps.frame (pointer pb n n) (UInt256.ofNat 3358)
    (UInt256.ofNat (pb-32)) (UInt256.ofNat (l1PC n)) z.tn (MachineState.readWord z.memory 128) inv tail
  have htail : tail.length ≤ 1006 := by simp only [tail, List.length_cons]; omega
  have hf := TnCacheFrameOps.run_flush 3963 st (pointer pb n n) (UInt256.ofNat 3358)
    (UInt256.ofNat (pb-32)) (UInt256.ofNat (l1PC n)) z.tn (MachineState.readWord z.memory 128) inv
    tail htail hact
  have g0 := TnM128CandidateBlocks.flush.steps
    (s := framed st (UInt256.ofNat 3963) stack) (env.transfer rfl rfl) rfl hf
  have hg := TnCacheExitTrace.run_guard aft 3968 (pointer pb n n)
    (UInt256.ofNat (pb-32)) (UInt256.ofNat (l1PC n)) z.tn (MachineState.readWord z.memory 128) inv tail htail
  have g1 := TnM128L1Blocks.guard.steps
    (s := framed aft (UInt256.ofNat 3968) stack) (env.transfer rfl rfl) rfl hg
  have hd := TnCacheExitTrace.run_drop aft 3977 (pointer pb n n) (UInt256.ofNat 3358)
    (UInt256.ofNat (pb-32)) (UInt256.ofNat (l1PC n)) z.tn (MachineState.readWord z.memory 128) inv
    m0 tl m96 m64 m32 aEnd dst ret rest hcap
  have g2 := TnM128L1Blocks.drop.steps
    (s := framed aft (UInt256.ofNat 3977) stack) (env.transfer rfl rfl) rfl hd
  simpa only [rowState, if_neg (Nat.lt_irrefl n), st, aft, stack, tail] using (g0.trans g1).trans g2

/-- The complete ordinary multiply loop and cache flush compute precisely the
existing machine-carry model. Setup and conditional subtraction are external. -/
noncomputable def multiply_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (pa pb n : Nat) (hn : n = 4 ∨ n = 8)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 2816)
    (hpbLift : pb+32*n ≤ 2080 ∨ 2112 ≤ pb)
    (ha : aEnd.toNat = pa+32*(n-1))
    (hc : Cached z.memory pa n tl inv m0 m96 m64 m32) :
    GasSteps (rowState s z pb n 0 tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (framed {s with memory := CarryRowModel.rowsCarry (lift z.memory z.tn) pa pb n n}
        (UInt256.ofNat 3991) (dst :: ret :: rest)) := by
  have hr := rows_steps s env z pa pb n hn tl inv m0 aEnd m96 m64 m32 dst ret rest
    hcap hact hpa hpb hfit ha hc n le_rfl
  have hf := finish_steps s env (rows z pa pb n n) pb n
    tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact
  have hlift := rows_lift z pa pb n n (by rcases hpa with h | rfl <;> omega)
    hpbLift (by omega) (by omega)
  have both := hr.trans hf
  rw [← hlift] at both
  exact both

#print axioms finish_steps
#print axioms multiply_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128MultiplySteps
