import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchRunZero
import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchRunJump
import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchRunCheck
import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchRunTail
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

open EvmSemantics
open EvmSemantics.EVM

private def gasSteps_zeroSetup (input : ByteArray)
    (hzero : modulusSize input = 0) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (zeroSetupState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka zeroSetupPath rfl rfl
      (run_zeroSetup input hzero) rfl deployAddress_not_precompile

private def gasSteps_zeroReturn (input : ByteArray) :
    Challenge.EvmProof.GasSteps (zeroSetupState input)
      (zeroSizeFinalState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka zeroReturnPath rfl rfl
      (run_zeroReturn input) rfl deployAddress_not_precompile

private theorem blockCost_of_static
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka))
    {s t : State} (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = .Osaka)
    (hfree : ∀ located ∈ path, Challenge.EvmProof.Meter.CopyFree located.instruction)
    (hcost : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work)
    (hactive : s.activeWords = t.activeWords) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s = work := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    path work hresult hfork hfree hcost
  rw [hactive] at hmeter
  omega

private theorem gasSteps_zeroSetup_cost (input : ByteArray)
    (hzero : modulusSize input = 0) :
    (gasSteps_zeroSetup input hzero).cost = 21 := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost zeroSetupPath
    (Main.headerState input) = 21
  exact blockCost_of_static zeroSetupPath 21 (run_zeroSetup input hzero)
    rfl (by decide) rfl rfl

@[simp] private theorem gasSteps_zeroReturn_cost (input : ByteArray) :
    (gasSteps_zeroReturn input).cost = 0 := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost zeroReturnPath
    (zeroSetupState input) = 0
  exact blockCost_of_static zeroReturnPath 0 (run_zeroReturn input)
    rfl (by decide) rfl rfl

def gasSteps_zeroSize (input : ByteArray) (hzero : modulusSize input = 0) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (zeroSizeFinalState input) :=
  (gasSteps_zeroSetup input hzero).trans (gasSteps_zeroReturn input)

set_option maxHeartbeats 5000000 in
theorem gasSteps_zeroSize_cost (input : ByteArray)
    (hzero : modulusSize input = 0) :
    (gasSteps_zeroSize input hzero).cost = 21 := by
  simp [gasSteps_zeroSize, gasSteps_zeroSetup_cost]

private def gasSteps_wordJump (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (wordDispatchState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka wordJumpPath rfl rfl
      (run_wordJump input hvalid hpositive) rfl deployAddress_not_precompile

private def gasSteps_wordCheck (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps (wordDispatchState input)
      (wordCheckedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka wordCheckPath rfl rfl
      (run_wordRest input hvalid hpositive hword) rfl deployAddress_not_precompile

private def gasSteps_wordTail (input : ByteArray) :
    Challenge.EvmProof.GasSteps (wordCheckedState input)
      (wordRouteEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka wordTailPath rfl rfl
      (run_wordTail input) rfl deployAddress_not_precompile

@[simp] private theorem gasSteps_wordJump_cost (input : ByteArray)
    (hvalid : ValidInput input) (hpositive : 0 < modulusSize input) :
    (gasSteps_wordJump input hvalid hpositive).cost = 17 := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost wordJumpPath
    (Main.headerState input) = 17
  exact blockCost_of_static wordJumpPath 17 (run_wordJump input hvalid hpositive)
    rfl (by decide) rfl rfl

@[simp] private theorem gasSteps_wordCheck_cost (input : ByteArray)
    (hvalid : ValidInput input) (hpositive : 0 < modulusSize input)
    (hword : modulusSize input ≤ 32) :
    (gasSteps_wordCheck input hvalid hpositive hword).cost = 41 := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost wordCheckPath
    (wordDispatchState input) = 41
  exact blockCost_of_static wordCheckPath 41 (run_wordRest input hvalid hpositive hword)
    rfl (by decide) rfl rfl

@[simp] private theorem gasSteps_wordTail_cost (input : ByteArray) :
    (gasSteps_wordTail input).cost = 32 := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost wordTailPath
    (wordCheckedState input) = 32
  exact blockCost_of_static wordTailPath 32 (run_wordTail input)
    rfl (by decide) rfl rfl

def gasSteps_wordRouteEnter (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    WordRouteEnter input :=
  (gasSteps_wordJump input hvalid hpositive).trans <|
    (gasSteps_wordCheck input hvalid hpositive hword).trans
      (gasSteps_wordTail input)

set_option maxHeartbeats 5000000 in
theorem gasSteps_wordRouteEnter_cost (input : ByteArray)
    (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    (gasSteps_wordRouteEnter input hvalid hpositive hword).cost = 90 := by
  simp [gasSteps_wordRouteEnter]

/-- Complete trace and exact minimum gas for zero-width results. -/
def gasSteps_zeroSize_total (input : ByteArray) (hvalid : ValidInput input)
    (hzero : modulusSize input = 0)
    (entry : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Main.trampolineState input 1196)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (zeroSizeFinalState input) :=
  (Main.gasSteps_header input hvalid entry).trans (gasSteps_zeroSize input hzero)

@[simp] theorem zeroSizeFinalState_isDone (input : ByteArray) :
    (zeroSizeFinalState input).isDone = true := by
  rfl

theorem zeroSizeFinalState_result (input : ByteArray)
    (hzero : modulusSize input = 0) :
    (zeroSizeFinalState input).toResult = .returned (spec input) := by
  simp [zeroSizeFinalState, spec, hzero]

end Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
