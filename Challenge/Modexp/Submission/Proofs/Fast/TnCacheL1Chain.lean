import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Trace
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandL1

set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Chain
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel StagedOperand
open TnCacheL1Trace

/-- A consecutive suffix of the staged first loop, retaining each JUMPDEST. -/
def program (n j0 : Nat) : Nat → List Instr
  | 0 => []
  | k+1 => program n j0 k ++ TnCacheL1Trace.stepProgram
      (UInt256.ofNat (32*(n-1-(j0+k)))) (UInt256.ofNat (2112+32*(n-1-(j0+k))))

theorem snapshot_l1Run_pres {q : MacState} {pa n : Nat}
    (h : Snapshot q.memory pa n) (bi : UInt256) (j0 : Nat) (hn : n ≤ 8)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368) :
    ∀ k, j0+k ≤ n → Snapshot (l1Run q bi pa n j0 k).memory pa n
  | 0, _ => h
  | k+1, hk => by
      rw [l1Run_succ]
      exact Snapshot.l1StepOn_pres_stage
        (snapshot_l1Run_pres h bi j0 hn hpa k (by omega))
        bi (j0+k) hn hpa (by omega)

theorem run_chain (s : State) (pc : Nat) (q : MacState) (bi : UInt256)
    (pa n j0 k : Nat) (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hactive : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : j0+k ≤ n)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368) (hsnapshot : Snapshot q.memory pa n) :
    runInstructions (program n j0 k)
      (TnCacheL1Trace.qState s (UInt256.ofNat pc) q bi pbi hd pbEnd flag tn destination returnPC rest) =
    some (TnCacheL1Trace.qState s (UInt256.ofNat (pc+37*k)) (l1Run q bi pa n j0 k)
      bi pbi hd pbEnd flag tn destination returnPC rest) := by
  induction k with
  | zero => simp [program, runInstructions, l1Run]
  | succ k ih =>
      have prev := ih (by omega)
      have hs := snapshot_l1Run_pres hsnapshot bi j0 hn hpa k (by omega)
      have hoff : (UInt256.ofNat (32*(n-1-(j0+k)))).toNat = 32*(n-1-(j0+k)) := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have ht : (UInt256.ofNat (2112+32*(n-1-(j0+k)))).toNat = 2112+32*(n-1-(j0+k)) := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have cell := TnCacheL1Trace.run_step s (UInt256.ofNat (pc+37*k)) (l1Run q bi pa n j0 k)
        bi pa n (j0+k) (UInt256.ofNat (32*(n-1-(j0+k))))
        (UInt256.ofNat (2112+32*(n-1-(j0+k)))) hoff ht pbi hd pbEnd flag tn
        destination returnPC rest hcap hactive hn (by omega) hs
      have both := runInstructions_append_some _ _ _ _ _ prev cell
      have hpc : pc+37*k+37 = pc+37*(k+1) := by omega
      simpa only [program, l1Run_succ, Challenge.EvmProof.Word.ofNat_add_mod, hpc] using both

#print axioms run_chain
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Chain
