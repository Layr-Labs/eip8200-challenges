import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.TnMod128Invariant
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnM128RowSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPreserves
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPointers

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace CycleSubmission.Global.Fast.TnM128RowsSteps
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open TnCacheRowModel TnCacheRowPreserves TnCacheRowPointers TnM128RowSteps
open TnM128ReductionSteps

def rowState (s : State) (z : CacheState) (n i : Nat)
    (w3 ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := z.memory}
    (if i < n then UInt256.ofNat (headPC n) else UInt256.ofNat 3414)
    (TnCacheFrameOps.frame (qptr n i) (UInt256.ofNat (headPC n)) w3
      ent m32 (MachineState.readWord z.memory 128) m64
      (m0 :: tl :: m96 :: inv :: z.tn :: aEnd :: dst :: ret :: rest))

theorem result_eq_row (z : CacheState) (pa n i : Nat) (hn : n ≤ 8) (hi : i < n) :
    result z.memory z.tn pa n (qptr n i) = row z pa 256 n i := by
  unfold result row TnCacheSquareModel.fromL1 rowBi TnCacheHeadTrace.bAddr
  rw [sub_qptr_toNat 224 n i hn (by norm_num), show 224+32*(n-i) = 256+32*(n-1-i) from by omega]

noncomputable def step (s : State)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (z : CacheState) (pa n i : Nat) (hn : n = 4) (hi : i < n)
    (w3 ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368)
    (ha : aEnd.toNat = pa+32*(n-1))
    (hc : Cached z.memory pa n tl inv m0 m96 m64 m32)
    (hw3 : n = 8 → w3 = MachineState.readWord z.memory 192) :
    GasSteps (rowState s z n i w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (rowState s (row z pa 256 n i) n (i+1) w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest) := by
  have hn8 : n ≤ 8 := by omega
  have hq : TnCacheHeadTrace.bAddr (qptr n i) ≤ 2784 := by
    unfold TnCacheHeadTrace.bAddr; rw [sub_qptr_toNat 224 n i hn8 (by norm_num)]; omega
  have hr := row_steps {s with memory := z.memory}
    (env.transfer rfl rfl) pa n hn (qptr n i) w3 ent z.tn
    (MachineState.readWord z.memory 128) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hq hpa ha
    hc.readonly hc.extra hc.inverse hc.snapshot rfl hw3
  have he := result_eq_row z pa n i hn8 hi
  have hcond := qptr_condition n i hn8 hi
  rw [qptr_succ n i hn8 hi] at hcond
  simpa only [rowState, if_pos hi, he, hcond, qptr_succ n i hn8 hi, TnMod128Invariant.row_read] using hr

/-- Every ordinary row executes once, with the cache still in the stack until
the common flush block. The theorem is uniform in four/eight limbs and row count. -/
noncomputable def rows_steps (s : State)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (z : CacheState) (pa n : Nat) (hn : n = 4)
    (w3 ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368)
    (ha : aEnd.toNat = pa+32*(n-1))
    (hc : Cached z.memory pa n tl inv m0 m96 m64 m32)
    (hw3 : n = 8 → w3 = MachineState.readWord z.memory 192) :
    ∀ i, i ≤ n → GasSteps (rowState s z n 0 w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (rowState s (rows z pa 256 n i) n i w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest)
  | 0, _ => .refl _
  | i+1, hi => by
      have prev := rows_steps s env z pa n hn w3 ent tl inv m0 aEnd m96 m64 m32 dst ret
        rest hcap hact hpa ha hc hw3 i (by omega)
      have next := step s env (rows z pa 256 n i) pa n i hn (by omega)
        w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hpa ha
        (hc.rows 256 i (by omega) hpa)
        (fun h => (hw3 h).trans (TnMod128Invariant.rows_read_low z pa 256 n i 192 (by decide)).symm)
      exact prev.trans next

end CycleSubmission.Global.Fast.TnM128RowsSteps
