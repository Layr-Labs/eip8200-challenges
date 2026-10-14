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

/-- st8: the mode test comes first (a multiply head falls through), then the carry flush and
the frame drop. -/
noncomputable def finish_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (n : Nat) (hn : n = 4 ∨ n = 8)
    (w3 ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (rowState s z n n w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (framed {s with memory := lift z.memory z.tn} (UInt256.ofNat 4135) (dst :: ret :: rest)) := by
  let tail := m0 :: tl :: m96 :: inv :: z.tn :: aEnd :: dst :: ret :: rest
  let st : State := {s with memory := z.memory}
  let aft : State := {s with memory := lift z.memory z.tn}
  let stack := TnCacheFrameOps.frame (qptr n n) (UInt256.ofNat (headPC n))
    w3 ent m32 (MachineState.readWord z.memory 128) m64 tail
  have htail : tail.length ≤ 1006 := by simp only [tail, List.length_cons]; omega
  have hhd : headPC n = 3545 ∨ headPC n = 5352 := by
    rcases hn with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hg := TnCacheExitTrace.run_guard st 4107 (headPC n) hhd (qptr n n)
    w3 ent m32 (MachineState.readWord z.memory 128) m64 tail htail
  have g0 := TnM128L1Blocks.guard.steps
    (s := framed st (UInt256.ofNat 4107) stack) (env.transfer rfl rfl) rfl hg
  have hf := TnCacheFrameOps.run_flush13 4116 st (qptr n n) (UInt256.ofNat (headPC n))
    w3 ent m32 (MachineState.readWord z.memory 128) m64
    m0 tl m96 inv z.tn (aEnd :: dst :: ret :: rest) (by simp only [List.length_cons]; omega) hact
  have g1 := TnM128CandidateBlocks.flush.steps
    (s := framed st (UInt256.ofNat 4116) stack) (env.transfer rfl rfl) rfl hf
  have hd := TnCacheExitTrace.run_drop aft 4121 (qptr n n) (UInt256.ofNat (headPC n))
    w3 ent m32 (MachineState.readWord z.memory 128) m64
    m0 tl m96 inv z.tn aEnd dst ret rest hcap
  have g2 := TnM128L1Blocks.drop.steps
    (s := framed aft (UInt256.ofNat 4121) stack) (env.transfer rfl rfl) rfl hd
  simpa only [rowState, if_neg (Nat.lt_irrefl n), st, aft, stack, tail] using (g0.trans g1).trans g2

/-- The complete ordinary multiply loop and cache flush compute precisely the
existing machine-carry model, the multiplier block at `0x100`. Setup and conditional
subtraction are external. -/
noncomputable def multiply_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (pa n : Nat) (hn : n = 4 ∨ n = 8)
    (w3 ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368)
    (ha : aEnd.toNat = pa+32*(n-1))
    (hc : Cached z.memory pa n tl inv m0 m96 m64 m32)
    (hw3 : n = 8 → w3 = MachineState.readWord z.memory 192) :
    GasSteps (rowState s z n 0 w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (framed {s with memory := CarryRowModel.rowsCarry (lift z.memory z.tn) pa 256 n n}
        (UInt256.ofNat 4135) (dst :: ret :: rest)) := by
  have hr := rows_steps s env z pa n hn w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest
    hcap hact hpa ha hc hw3 n le_rfl
  have hf := finish_steps s env (rows z pa 256 n n) n hn
    w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact
  have hlift := rows_lift z pa 256 n n (by rcases hpa with h | rfl <;> omega)
    (Or.inl (by omega)) (by omega) (by omega)
  have both := hr.trans hf
  rw [← hlift] at both
  exact both

#print axioms finish_steps
#print axioms multiply_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128MultiplySteps
