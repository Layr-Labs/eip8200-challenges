import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Trace0
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Trace1
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Trace2
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024BranchIsZero
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024BranchPush
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024BranchJumpTaken
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024BranchJumpNotTaken
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Fallback
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Return

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024Trace

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard1024Logic Guard1024State Guard1024Paths

private def sound {s t : State} (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka))
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

private def soundOne {s t : State}
    {located : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka}
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocated located s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocated_sound hcode hfork h hrun hnp

def gasSteps_match (input : ByteArray) (h : guardDiff input = 0) :
    Challenge.EvmProof.GasSteps (entryState input) (returnedState input) :=
  ((((sound preludePath rfl (Guard1024Trace0.run_prelude input) rfl rfl deployAddress_not_precompile).trans
    (sound check0Path rfl (Guard1024Trace0.run_check0 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (Guard1024Trace1.run_check1 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (Guard1024Trace2.run_check2 input) rfl rfl deployAddress_not_precompile)).trans
    ((sound branchIsZeroPath rfl (Guard1024Branch.run_iszero_match input h) rfl rfl deployAddress_not_precompile).trans
      ((soundOne rfl (Guard1024Branch.run_push input (UInt256.ofNat 1)) rfl rfl deployAddress_not_precompile).trans
        ((soundOne rfl (Guard1024Branch.run_jump_taken input) rfl rfl deployAddress_not_precompile).trans
          (sound returnPath rfl (Guard1024Return.run_return input) rfl rfl deployAddress_not_precompile))))

def gasSteps_fallback (input : ByteArray) (h : guardDiff input ≠ 0) :
    Challenge.EvmProof.GasSteps (entryState input) (fallbackState input) :=
  ((((sound preludePath rfl (Guard1024Trace0.run_prelude input) rfl rfl deployAddress_not_precompile).trans
    (sound check0Path rfl (Guard1024Trace0.run_check0 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (Guard1024Trace1.run_check1 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (Guard1024Trace2.run_check2 input) rfl rfl deployAddress_not_precompile)).trans
    ((sound branchIsZeroPath rfl (Guard1024Branch.run_iszero_mismatch input h) rfl rfl deployAddress_not_precompile).trans
      ((soundOne rfl (Guard1024Branch.run_push input (UInt256.ofNat 0)) rfl rfl deployAddress_not_precompile).trans
        ((soundOne rfl (Guard1024Branch.run_jump_notTaken input) rfl rfl deployAddress_not_precompile).trans
          (sound fallbackPath rfl (Guard1024Fallback.run_fallback input) rfl rfl deployAddress_not_precompile))))

end Challenge.Modexp.Submission.Proofs.Fast.Guard1024Trace
