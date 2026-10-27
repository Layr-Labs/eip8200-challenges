import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCoreRight0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SiteRight0
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CoreRight0
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCoreRight0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
def gasSteps (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (halias : rho[2]? = some q.b) (haliasC : rho[1]? = some q.c)
    (haliasD : rho[0]? = some q.d) (haliasA : rho[3]? = some q.a) (hh4 : h4 = q.e)
    (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hz : PadZero s.memory) :
    GasSteps {s with pc := UInt256.ofNat 4602, stack := stack s.memory h4 [ .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .e ] q right (UInt256.ofNat 1352829926) rho}
      {s with pc := UInt256.ofNat 4634, stack := stack s.memory h4 [ .b, .e, .d, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (StaggerCoreModel.right0 s.memory q) (right) (UInt256.ofNat 1352829926) rho} := by
  have h := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SiteRight0.gasSteps s (input s.memory h4 q right (UInt256.ofNat 1352829926)) rho hs halias haliasC haliasD haliasA (by rfl) hh4 hr ha hcode hfork hnp hz
  rw [output_eq] at h
  exact h
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CoreRight0
