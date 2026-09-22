import Challenge.Modexp.Submission.Proofs.Fast.TnMod128Invariant
import Challenge.Modexp.Submission.Proofs.Fast.TnM128RowSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPreserves
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPointers

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128RowsSteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open TnCacheRowModel TnCacheRowPreserves TnCacheRowPointers TnM128RowSteps
open TnM128ReductionSteps

def rowState (s : State) (z : CacheState) (pb n i : Nat)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := z.memory}
    (if i < n then UInt256.ofNat 3533 else UInt256.ofNat 4128)
    (TnCacheFrameOps.frame (pointer pb n i) (UInt256.ofNat 3533) (UInt256.ofNat (pb-32))
      (UInt256.ofNat (l1PC n)) z.tn (MachineState.readWord z.memory 128) inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))

theorem result_eq_row (z : CacheState) (pa pb n i : Nat)
    (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 2816) (hi : i < n) :
    result z.memory z.tn pa n (pointer pb n i) = row z pa pb n i := by
  unfold result row TnCacheSquareModel.fromL1 rowBi
  rw [pointer_limb pb n i hpb hfit hi]

noncomputable def step (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (pa pb n i : Nat) (hn : n = 4 ∨ n = 8) (hi : i < n)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 2816)
    (ha : aEnd.toNat = pa+32*(n-1))
    (hc : Cached z.memory pa n tl inv m0 m96 m64 m32) :
    GasSteps (rowState s z pb n i tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (rowState s (row z pa pb n i) pb n (i+1) tl inv m0 aEnd m96 m64 m32 dst ret rest) := by
  have hpbi : (pointer pb n i).toNat ≤ 2784 := by
    rw [pointer_limb pb n i hpb hfit hi]
    omega
  have hr := row_steps {s with memory := z.memory}
    (env.transfer rfl rfl) pa n hn (pointer pb n i) (UInt256.ofNat (pb-32)) z.tn
    (MachineState.readWord z.memory 128) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hpbi hpa ha
    hc.readonly hc.extra hc.inverse hc.snapshot rfl
  have he := result_eq_row z pa pb n i hpb hfit hi
  have hcond := pointer_condition pb n i hpb hfit hi
  rw [pointer_succ] at hcond
  simpa only [rowState, if_pos hi, he, hcond, pointer_succ, TnMod128Invariant.row_read] using hr

/-- Every ordinary row executes once, with the cache still in the stack until
the common flush block. The theorem is uniform in four/eight limbs and row count. -/
noncomputable def rows_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (pa pb n : Nat) (hn : n = 4 ∨ n = 8)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 2816)
    (ha : aEnd.toNat = pa+32*(n-1))
    (hc : Cached z.memory pa n tl inv m0 m96 m64 m32) :
    ∀ i, i ≤ n → GasSteps (rowState s z pb n 0 tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (rowState s (rows z pa pb n i) pb n i tl inv m0 aEnd m96 m64 m32 dst ret rest)
  | 0, _ => .refl _
  | i+1, hi => by
      have prev := rows_steps s env z pa pb n hn tl inv m0 aEnd m96 m64 m32 dst ret
        rest hcap hact hpa hpb hfit ha hc i (by omega)
      have next := step s env (rows z pa pb n i) pa pb n i hn (by omega)
        tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hpa hpb hfit ha
        (hc.rows pb i (by omega) hpa)
      exact prev.trans next

#print axioms step
#print axioms rows_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128RowsSteps
