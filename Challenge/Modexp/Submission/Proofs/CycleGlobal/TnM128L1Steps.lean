import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnM128L1Blocks

noncomputable section
set_option warningAsError true
set_option maxRecDepth 36470
set_option maxHeartbeats 3647000

namespace CycleSubmission.Global.Fast.TnM128L1Steps
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel StagedOperand
open TnM128L1Blocks

noncomputable def private_steps (s : State)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (q : MacState) (bi : UInt256) (pa : Nat)
    (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hactive : 88 ≤ s.activeWords.toNat)
    (hpa : pa+32*4 ≤ 2048 ∨ pa = 2368) (hsnapshot : Snapshot q.memory pa 4) :
    GasSteps
      (TnCacheL1Trace.qState s (UInt256.ofNat 3809) q bi
        pbi hd pbEnd flag tn destination returnPC rest)
      (TnCacheL1Suffix.qStateLast s (UInt256.ofNat 3916) (l1Run q bi pa 4 1 3)
        pbi hd pbEnd flag tn destination returnPC rest) := by
  have hr := TnCacheL1Suffix.run_private3 s 3809 q bi pa
    pbi hd pbEnd flag tn destination returnPC rest hcap hactive hpa hsnapshot
  exact private3.steps
    (s := TnCacheL1Trace.qState s (UInt256.ofNat 3809) q bi
      pbi hd pbEnd flag tn destination returnPC rest)
    (env.transfer rfl rfl) rfl hr

end CycleSubmission.Global.Fast.TnM128L1Steps
