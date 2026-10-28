import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCoreUnpack
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullSiteUnpack
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCoreUnpack
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCoreUnpack
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
def gasSteps (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps {s with pc := UInt256.ofNat 10133, stack := stack s.memory h4 [ .d, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (StaggerAlgorithm.physicalKey 76) rho}
      {s with pc := UInt256.ofNat 10134, stack := stack s.memory h4 [ .factor, .dr, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (StaggerCoreModel.left q) (q) (UInt256.ofNat 2840853838) rho} := by
  have h := PadCopy.FullSiteUnpack.gasSteps s (input s.memory h4 q right (StaggerAlgorithm.physicalKey 76)) rho hs hr ha hcode hfork hnp hz
  rw [output_eq] at h
  exact h

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCoreUnpack
