import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCorePaired16
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullSitePaired16
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCorePaired16
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCorePaired16
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
def gasSteps (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps {s with pc := UInt256.ofNat 5428, stack := stack s.memory h4 [ .d, .cache 140, .e, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (StaggerAlgorithm.physicalKey 15) rho}
      {s with pc := UInt256.ofNat 5488, stack := stack s.memory h4 [ .d, .cache 140, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval s.memory q) right (StaggerAlgorithm.physicalKey 16) rho} := by
  have hk : (input s.memory h4 q right (StaggerAlgorithm.physicalKey 15)).v5 = UInt256.ofNat 34535016170389834383797866734609369064725060249452544 := by
    change StaggerAlgorithm.physicalKey 15 = _
    decide
  have g := PadCopy.FullSitePaired16.gasSteps s (input s.memory h4 q right (StaggerAlgorithm.physicalKey 15))
    rho hstack hrun hactive hk hcode hfork hnp hz (by change MachineState.readWord s.memory 360 = _; exact hz 20 (by decide))
  rw [output_eq] at g
  exact g

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCorePaired16
