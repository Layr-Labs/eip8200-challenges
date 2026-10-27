import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCoreLeft79
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullSiteLeft79
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCoreLeft79
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCoreLeft79
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
def gasSteps (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) (hsame : right.d = q.a)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps {s with pc := UInt256.ofNat 7975, stack := stack s.memory h4 [ .d, .b, .c, .e, .a, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .k, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190 ] q right (UInt256.ofNat 2840853838) (h4 :: rho)}
      {s with pc := UInt256.ofNat 7994, stack := stack s.memory h4 [ .b, .c, .d, .a, .dr, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .e, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (left79Raw s.memory q) (right) (UInt256.ofNat 2840853838) rho} := by
  have h := PadCopy.FullSiteLeft79.gasSteps s (input s.memory h4 q right (UInt256.ofNat 2840853838)) (h4 :: rho) (by simp only [List.length_cons]; omega) hr ha hcode hfork hnp hz (by change MachineState.readWord s.memory 360 = _; exact hz 20 (by decide))
  rw [output_eq s.memory h4 q right rho hsame] at h
  exact h

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullCoreLeft79
