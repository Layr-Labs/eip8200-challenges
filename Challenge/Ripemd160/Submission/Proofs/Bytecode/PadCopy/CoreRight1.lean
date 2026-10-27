import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCoreRight1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SiteRight1
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CoreRight1
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCoreRight1
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
def gasSteps (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (halias : rho[2]? = some q.c) (hh4 : h4 = q.a) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hz : PadZero s.memory) :
    GasSteps {s with pc := UInt256.ofNat 4634, stack := stack s.memory h4 [ .b, .e, .d, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (UInt256.ofNat 1352829926) rho}
      {s with pc := UInt256.ofNat 4674, stack := stack s.memory h4 [ .d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (StaggerCoreModel.right1 s.memory q) (right) (UInt256.ofNat 1352829926) rho} := by
  have h := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SiteRight1.gasSteps s (input s.memory h4 q right (UInt256.ofNat 1352829926)) rho hs halias (by rfl) hh4.symm hr ha hcode hfork hnp hz
  rw [output_eq] at h
  exact h
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CoreRight1
