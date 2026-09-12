import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPackBridge
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCoreBody
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired80WordRound
open StaggerPersistentPackBridge (suffix)

def gasSteps (s : State) (h : WordLane) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 894) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (StaggerPersistentCoreRight.initialState s h.e h (suffix h off limit rho))
      (StaggerCore.suffixState s h.e (StaggerCoreModel.paired s.memory h) (suffix h off limit rho)) := by
  have hstack : (suffix h off limit rho).length ≤ 900 := by
    simp only [suffix, List.length_append, List.length_cons, List.length_nil]
    omega
  have gr := StaggerPersistentCoreRight.gasSteps s h.e h (suffix h off limit rho)
    hstack hr ha hcode hfork hnp
  have gp := StaggerPersistentPackBridge.gasSteps s h (StaggerCoreModel.prologue s.memory h)
    off limit rho (by omega) hr hcode hfork hnp
  have gc := StaggerCore.gasSteps_pairedSuffix s h.e
    (StaggerCoreModel.pair h (StaggerCoreModel.prologue s.memory h)) h (suffix h off limit rho)
    hstack hr ha hcode hfork hnp
  exact gr.trans (gp.trans gc)
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCoreBody
