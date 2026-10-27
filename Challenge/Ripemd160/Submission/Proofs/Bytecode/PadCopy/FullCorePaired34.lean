import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCorePaired34
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullSitePaired34
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCorePaired34
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCorePaired34
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
def gasSteps (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps {s with pc := UInt256.ofNat 6249, stack := stack s.memory h4 [ .d, .factor, .cache 350, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (StaggerAlgorithm.physicalKey 33) rho}
      {s with pc := UInt256.ofNat 6281, stack := stack s.memory h4 [ .d, .factor, .cache 350, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval s.memory q) right (StaggerAlgorithm.physicalKey 34) rho} := by
  have g := PadCopy.FullSitePaired34.gasSteps s (input s.memory h4 q right (StaggerAlgorithm.physicalKey 33))
    rho hstack hrun hactive hcode hfork hnp hz
  rw [output_eq] at g
  exact g

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCorePaired34
