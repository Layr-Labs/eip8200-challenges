import Challenge.Modexp.Submission.Proofs.Fast.GuardTrace0
import Challenge.Modexp.Submission.Proofs.Fast.GuardTrace1
import Challenge.Modexp.Submission.Proofs.Fast.GuardTrace2
import Challenge.Modexp.Submission.Proofs.Fast.GuardTrace3
import Challenge.Modexp.Submission.Proofs.Fast.GuardTrace4
import Challenge.Modexp.Submission.Proofs.Fast.GuardBranchIsZero
import Challenge.Modexp.Submission.Proofs.Fast.GuardBranchPush
import Challenge.Modexp.Submission.Proofs.Fast.GuardBranchJumpTaken
import Challenge.Modexp.Submission.Proofs.Fast.GuardBranchJumpNotTaken
import Challenge.Modexp.Submission.Proofs.Fast.GuardFallback
import Challenge.Modexp.Submission.Proofs.Fast.GuardReturn

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardTrace

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardLogic GuardState GuardPaths

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
  ((((((sound preludePath rfl (GuardTrace0.run_prelude input) rfl rfl deployAddress_not_precompile).trans
    (sound check0Path rfl (GuardTrace0.run_check0 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (GuardTrace1.run_check1 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (GuardTrace2.run_check2 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check3Path rfl (GuardTrace3.run_check3 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check4Path rfl (GuardTrace4.run_check4 input) rfl rfl deployAddress_not_precompile)).trans
    ((sound branchIsZeroPath rfl (GuardBranch.run_iszero_match input h) rfl rfl deployAddress_not_precompile).trans
      ((soundOne rfl (GuardBranch.run_push input (UInt256.ofNat 1)) rfl rfl deployAddress_not_precompile).trans
        ((soundOne rfl (GuardBranch.run_jump_taken input) rfl rfl deployAddress_not_precompile).trans
          (sound returnPath rfl (GuardReturn.run_return input) rfl rfl deployAddress_not_precompile))))

def gasSteps_fallback (input : ByteArray) (h : guardDiff input ≠ 0) :
    Challenge.EvmProof.GasSteps (entryState input) (fallbackState input) :=
  ((((((sound preludePath rfl (GuardTrace0.run_prelude input) rfl rfl deployAddress_not_precompile).trans
    (sound check0Path rfl (GuardTrace0.run_check0 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (GuardTrace1.run_check1 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (GuardTrace2.run_check2 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check3Path rfl (GuardTrace3.run_check3 input) rfl rfl deployAddress_not_precompile)).trans
    (sound check4Path rfl (GuardTrace4.run_check4 input) rfl rfl deployAddress_not_precompile)).trans
    ((sound branchIsZeroPath rfl (GuardBranch.run_iszero_mismatch input h) rfl rfl deployAddress_not_precompile).trans
      ((soundOne rfl (GuardBranch.run_push input (UInt256.ofNat 0)) rfl rfl deployAddress_not_precompile).trans
        ((soundOne rfl (GuardBranch.run_jump_notTaken input) rfl rfl deployAddress_not_precompile).trans
          (sound fallbackPath rfl (GuardFallback.run_fallback input) rfl rfl deployAddress_not_precompile))))

end Challenge.Modexp.Submission.Proofs.Fast.GuardTrace
