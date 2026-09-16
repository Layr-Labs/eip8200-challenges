import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreRight0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreRight1
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCoreRight
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Paired144WordRound StaggerCoreCommon StaggerCoreModel

def initialState (s : State) (h4 : UInt256) (q : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 897, stack := stack s.memory h4 [ .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .e ] q q (UInt256.ofNat 1352829926) rho}

def finalState (s : State) (h4 : UInt256) (q : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 974, stack := stack s.memory h4 [ .d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (right1 s.memory (right0 s.memory q)) q (UInt256.ofNat 1352829926) rho}

def gasSteps (s : State) (h4 : UInt256) (q : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (halias : rho[2]? = some q.b) (haliasC : rho[1]? = some q.c)
    (haliasD : rho[0]? = some q.d) (haliasA : rho[3]? = some q.a) (hh4 : h4 = q.e)
    (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (initialState s h4 q rho) (finalState s h4 q rho) := by
  have g0 := StaggerCoreRight0.gasSteps s h4 q q rho hs halias haliasC haliasD haliasA hh4 hr ha hcode hfork hnp
  have g1 := StaggerCoreRight1.gasSteps s h4 (right0 s.memory q) q rho hs halias hh4 hr ha hcode hfork hnp
  exact g0.trans g1
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCoreRight
