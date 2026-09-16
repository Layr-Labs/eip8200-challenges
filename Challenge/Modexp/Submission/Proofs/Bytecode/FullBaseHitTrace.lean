import Challenge.Modexp.Submission.Proofs.Fast.FullBaseGuardCore
import Challenge.Modexp.Submission.Proofs.Fast.FullBasePaths

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Concrete located traces for the full-width-base hit branch

This module connects the small symbolic helper blocks to the submitted
artifact.  The inherited ADDMOD and Montgomery-product calls are deliberately
left as opaque boundaries; their existing subroutine contracts compose with
the three traces below.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FullBaseHitTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FullBase


private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

