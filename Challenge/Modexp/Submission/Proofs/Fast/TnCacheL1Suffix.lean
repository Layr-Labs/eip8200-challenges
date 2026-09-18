import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Chain

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Suffix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel StagedOperand
open TnCacheL1Trace

theorem program_eq (n j0 m i0 k : Nat)
    (hn : j0+k ≤ n) (hm : i0+k ≤ m) (he : n-j0 = m-i0) :
    TnCacheL1Chain.program n j0 k = TnCacheL1Chain.program m i0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hp := ih (by omega) (by omega)
      have ho : n-1-(j0+k) = m-1-(i0+k) := by omega
      simp only [TnCacheL1Chain.program, hp, ho]

/-- The shared last k staged MAC cells, including the reduction entry JUMPDEST. -/
def program (k : Nat) : List Instr :=
  TnCacheL1Chain.program 8 (8-k) k ++ [.op .JUMPDEST]

theorem run_suffix (s : State) (pc : Nat) (q : MacState) (bi : UInt256)
    (pa n j0 k : Nat) (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hactive : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : j0+k = n)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368) (hsnapshot : Snapshot q.memory pa n) :
    runInstructions (program k)
      (TnCacheL1Trace.qState s (UInt256.ofNat pc) q bi pbi hd pbEnd flag tn destination returnPC rest) =
    some (TnCacheL1Trace.qState s (UInt256.ofNat (pc+37*k+1)) (l1Run q bi pa n j0 k)
      bi pbi hd pbEnd flag tn destination returnPC rest) := by
  have chain := TnCacheL1Chain.run_chain s pc q bi pa n j0 k
    pbi hd pbEnd flag tn destination returnPC rest hcap hactive hn (by omega) hpa hsnapshot
  have hp := program_eq n j0 8 (8-k) k (by omega) (by omega) (by omega)
  rw [hp] at chain
  have hc : rest.length+10 < 1024 := by omega
  have hd : runInstructions [.op .JUMPDEST]
      (TnCacheL1Trace.qState s (UInt256.ofNat (pc+37*k)) (l1Run q bi pa n j0 k)
        bi pbi hd pbEnd flag tn destination returnPC rest) =
      some (TnCacheL1Trace.qState s (UInt256.ofNat (pc+37*k+1)) (l1Run q bi pa n j0 k)
        bi pbi hd pbEnd flag tn destination returnPC rest) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, TnCacheL1Trace.qState, hc,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  exact runInstructions_append_some _ _ _ _ _ chain hd

#print axioms run_suffix
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Suffix
