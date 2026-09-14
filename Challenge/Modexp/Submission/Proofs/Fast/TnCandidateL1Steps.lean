import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateL1Blocks

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateL1Steps
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel StagedOperand
open TnCandidateL1Blocks

def suffix (k : Nat) (hk : k ≤ 7) :
    Block TnCandidateArtifact.submissionArtifact .Osaka (3999-37*k) (TnCacheL1Suffix.program k) := by
  interval_cases k
  · exact suffix0
  · exact suffix1
  · exact suffix2
  · exact suffix3
  · exact suffix4
  · exact suffix5
  · exact suffix6
  · exact suffix7

noncomputable def suffix_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (q : MacState) (bi : UInt256) (pa n j0 k : Nat) (hk7 : k ≤ 7)
    (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hactive : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : j0+k = n)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368) (hsnapshot : Snapshot q.memory pa n) :
    GasSteps
      (TnCacheL1Trace.qState s (UInt256.ofNat (3999-37*k)) q bi
        pbi hd pbEnd flag tn destination returnPC rest)
      (TnCacheL1Trace.qState s (UInt256.ofNat 4000) (l1Run q bi pa n j0 k)
        bi pbi hd pbEnd flag tn destination returnPC rest) := by
  have hr := TnCacheL1Suffix.run_suffix s (3999-37*k) q bi pa n j0 k
    pbi hd pbEnd flag tn destination returnPC rest hcap hactive hn hk hpa hsnapshot
  have hpc : 3999-37*k+37*k+1 = 4000 := by omega
  rw [hpc] at hr
  exact (suffix k hk7).steps
    (s := TnCacheL1Trace.qState s (UInt256.ofNat (3999-37*k)) q bi
      pbi hd pbEnd flag tn destination returnPC rest)
    (env.transfer rfl rfl) rfl hr

#print axioms suffix_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateL1Steps
