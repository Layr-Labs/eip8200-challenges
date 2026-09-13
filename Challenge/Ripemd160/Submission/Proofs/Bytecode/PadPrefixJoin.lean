import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixJump
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixJoin
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
def gasSteps (s : State) (rho : List UInt256) (hs : rho.length ≤ 1019)
    (hr : s.halt = .Running)
    (hc : s.executionEnv.code = Artifact.submissionArtifact.code) (hf : s.fork = .Osaka)
    (hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 6779, stack := rho}
      {s with pc := UInt256.ofNat 2862, stack := rho} :=
  (PadPrefixJump.gasSteps_jump s rho (by omega) hr hc hf hn).trans
    (PadPrefixJoinDest.gasSteps_prefix s rho hs hr hc hf hn)
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixJoin
