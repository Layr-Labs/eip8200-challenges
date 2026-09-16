import Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks

set_option warningAsError true
set_option maxRecDepth 36470
set_option maxHeartbeats 3647000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Steps
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel StagedOperand
open TnM128L1Blocks

def suffix (k : Nat) (hk : k ≤ 7) :
    Block TnM128CandidateArtifact.submissionArtifact .Osaka (3646-37*k) (TnCacheL1Suffix.program k) := by
  interval_cases k
  · exact common0
  · exact common1
  · exact common2
  · exact common3
  · exact common4
  · exact common5
  · exact common6
  · exact common7

noncomputable def suffix_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (q : MacState) (bi : UInt256) (pa n j0 k : Nat) (hk7 : k ≤ 7)
    (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hactive : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : j0+k = n)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368) (hsnapshot : Snapshot q.memory pa n) :
    GasSteps
      (TnCacheL1Trace.qState s (UInt256.ofNat (3646-37*k)) q bi
        pbi hd pbEnd flag tn destination returnPC rest)
      (TnCacheL1Trace.qState s (UInt256.ofNat 3647) (l1Run q bi pa n j0 k)
        bi pbi hd pbEnd flag tn destination returnPC rest) := by
  have hr := TnCacheL1Suffix.run_suffix s (3646-37*k) q bi pa n j0 k
    pbi hd pbEnd flag tn destination returnPC rest hcap hactive hn hk hpa hsnapshot
  have hpc : 3646-37*k+37*k+1 = 3647 := by omega
  rw [hpc] at hr
  exact (suffix k hk7).steps
    (s := TnCacheL1Trace.qState s (UInt256.ofNat (3646-37*k)) q bi
      pbi hd pbEnd flag tn destination returnPC rest)
    (env.transfer rfl rfl) rfl hr

def privateSuffix (k : Nat) (hk : k ≤ 3) :
    Block TnM128CandidateArtifact.submissionArtifact .Osaka (5290-37*k) (TnCacheL1Suffix.program k) := by
  interval_cases k
  · exact private0
  · exact private1
  · exact private2
  · exact private3

noncomputable def private_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (q : MacState) (bi : UInt256) (pa n j0 k : Nat) (hk7 : k ≤ 3)
    (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hactive : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : j0+k = n)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368) (hsnapshot : Snapshot q.memory pa n) :
    GasSteps
      (TnCacheL1Trace.qState s (UInt256.ofNat (5290-37*k)) q bi
        pbi hd pbEnd flag tn destination returnPC rest)
      (TnCacheL1Trace.qState s (UInt256.ofNat 5291) (l1Run q bi pa n j0 k)
        bi pbi hd pbEnd flag tn destination returnPC rest) := by
  have hr := TnCacheL1Suffix.run_suffix s (5290-37*k) q bi pa n j0 k
    pbi hd pbEnd flag tn destination returnPC rest hcap hactive hn hk hpa hsnapshot
  have hpc : 5290-37*k+37*k+1 = 5291 := by omega
  rw [hpc] at hr
  exact (privateSuffix k hk7).steps
    (s := TnCacheL1Trace.qState s (UInt256.ofNat (5290-37*k)) q bi
      pbi hd pbEnd flag tn destination returnPC rest)
    (env.transfer rfl rfl) rfl hr

#print axioms suffix_steps
#print axioms private_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Steps
