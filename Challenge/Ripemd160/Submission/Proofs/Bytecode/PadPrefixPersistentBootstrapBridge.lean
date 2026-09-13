import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixContract
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixPersistentBootstrapEntry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixPersistentCoreBody
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixPersistentBootstrapBridge
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound Paired144WordRotation StaggerCoreCommon

def gasSteps_body (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 894) (hr : s.halt = .Running)
    (ha : 35 ≤ s.activeWords.toNat) (hz : PadPrefixContract.ZeroLoads s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s h off limit rho)
      (PadPrefixCore.suffixState s (Word.ofUInt32 h.h4)
        (StaggerCoreModel.paired s.memory (initial h))
        (StaggerPersistentFrame.coreRest h off limit rho)) := by
  have gb := gasSteps s h off limit rho (by omega) hr (by omega) hcode hfork hnp
  have gc := PadPrefixPersistentCoreBody.gasSteps s (initial h) off limit rho hs hr ha hz hcode hfork hnp
  have he : (initial h).e = Word.ofUInt32 h.h4 := by rw [initial_eq]
  have hsuf : PadPrefixPersistentPackBridge.suffix (initial h) off limit rho =
      StaggerPersistentFrame.coreRest h off limit rho := by
    rw [initial_eq]
    rfl
  rw [he, hsuf] at gc
  exact gb.trans gc

#print axioms gasSteps_body
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixPersistentBootstrapBridge
