import Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlRun
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

/-!
# Fixed-width route control-flow trace

The width guard is split into three short traces: accumulation, conditional
branch, and the legacy fallback jump.  A window hit is deliberately outside
this module.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlTrace

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running := by rfl)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

private def exactEnvironment (input : ByteArray) :
    WindowTwentyOneBinding.Environment Artifact.submissionArtifact .Osaka
      (Main.headerState input) where
  sizeBound := by
    change submissionBytecode.size < 2 ^ 256
    rw [submissionBytecode_size]
    norm_num
  code := rfl
  forkEq := rfl
  running := rfl
  noPrecompile := deployAddress_not_precompile

def gasSteps_miss (input : ByteArray) (hvalid : ValidInput input)
    (hmatch : ¬ WindowTwentyOneInput.Matches input)
    (hexact : ¬ WindowTwentyOneInput.ExactCase input) :
    Dispatch.WordRouteMiss input := by
  have h := WindowTwentyOneGasRoute.steps_miss Artifact.twentyOnePaths
    (Main.headerState input) (exactEnvironment input) input hvalid hmatch hexact
  simpa [WindowTwentyOnePositive.state, WindowTwentyOnePositive.context,
    WindowTwentyOnePositive.routeStack, Dispatch.wordRouteEntryState,
    Dispatch.wordEntryState] using h
/-- Successful fixed-width guard, before the modulus branch. -/
def gasSteps_hit (input : ByteArray) (hmatch : WindowGuardLogic.Matches input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordRouteEntryState input)
      (hitState input) :=
  (sound guardPath (run_guard input)).trans
    (sound branchPath (run_branch_match input hmatch))

/-- Concrete control half of the fixed-width route. -/
def control : WindowRoute.Control where
  enter := Dispatch.gasSteps_wordRouteEnter
  miss := fun input hvalid _ _ hmatch hexact =>
    gasSteps_miss input hvalid hmatch hexact

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlTrace
