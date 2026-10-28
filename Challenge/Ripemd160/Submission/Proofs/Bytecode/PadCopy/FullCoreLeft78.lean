import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCoreLeft78
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullSiteLeft78
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCoreLeft78
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCoreLeft78
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
def gasSteps (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) (hsame : right.e = q.a) (hsame2 : right.d = q.e) (hsame3 : right.b = q.c)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps {s with pc := UInt256.ofNat 10162, stack := stack s.memory h4 [ .b, .d, .e, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (UInt256.ofNat 2840853838) rho}
      {s with pc := UInt256.ofNat 10188, stack := stack s.memory h4 [ .d, .b, .c, .e, .a, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .k, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190 ] (StaggerCoreModel.left78 s.memory q) (right) (UInt256.ofNat 2840853838) (h4 :: rho)} := by
  have h := PadCopy.FullSiteLeft78.gasSteps s (input s.memory h4 q right (UInt256.ofNat 2840853838)) rho hs hr ha hcode hfork hnp hz (by change MachineState.readWord s.memory 360 = _; exact hz 20 (by decide))
  rw [output_eq s.memory h4 q right rho hsame hsame2 hsame3] at h
  exact h

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCoreLeft78
