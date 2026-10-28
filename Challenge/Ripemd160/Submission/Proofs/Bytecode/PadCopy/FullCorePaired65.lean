import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCorePaired65
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullSitePaired65
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCorePaired65
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCorePaired65
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero PadWord0)
def gasSteps (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) (hw : PadWord0 s.memory) :
    GasSteps {s with pc := UInt256.ofNat 7561, stack := stack s.memory h4 [ .d, .cache 350, .e, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (StaggerAlgorithm.physicalKey 64) rho}
      {s with pc := UInt256.ofNat 7610, stack := stack s.memory h4 [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval s.memory q) right (StaggerAlgorithm.physicalKey 65) rho} := by
  have g := PadCopy.FullSitePaired65.gasSteps s (input s.memory h4 q right (StaggerAlgorithm.physicalKey 64))
    rho hstack hrun hactive hcode hfork hnp hz
    (by change StaggerAlgorithm.physicalKey 64 = _; decide) hw.r522
  rw [output_eq] at g
  exact g

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCorePaired65
