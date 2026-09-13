import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixContract
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixPersistentPackBridge
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixPersistentCoreBody
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open PadPrefixPersistentPackBridge (suffix)

def gasSteps (s : State) (h : WordLane) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 894) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat) (hz : PadPrefixContract.ZeroLoads s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (PadPrefixPersistentCoreRight.initialState s h.e h (suffix h off limit rho))
      (PadPrefixCore.suffixState s h.e (StaggerCoreModel.paired s.memory h) (suffix h off limit rho)) := by
  have hstack : (suffix h off limit rho).length ≤ 900 := by
    simp only [suffix, JointRightPackModel.suffix, List.length_append, List.length_cons, List.length_nil]
    omega
  have gr := PadPrefixPersistentCoreRight.gasSteps s h.e h (suffix h off limit rho)
    hstack (by rfl) hr ha hcode hfork hnp
  have gp := PadPrefixPersistentPackBridge.gasSteps s h (StaggerCoreModel.right1 s.memory (StaggerCoreModel.right0 s.memory h))
    off limit rho (by omega) hr ha hcode hfork hnp
  have gc := PadPrefixCore.gasSteps_pairedSuffix s h.e
    (StaggerCoreModel.pair h (StaggerCoreModel.prologue s.memory h)) h (suffix h off limit rho)
    hstack hr ha hz hcode hfork hnp
  exact gr.trans (gp.trans gc)
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixPersistentCoreBody
