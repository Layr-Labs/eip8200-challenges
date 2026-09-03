import Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesLow
import Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesHigh
import Challenge.Modexp.Submission.Proofs.Bytecode.MainHeaderLoad
import Challenge.Modexp.Submission.Proofs.Bytecode.MainHeaderCheck
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

private def gasSteps_tramp0 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (trampolineState input 1196) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp0Path rfl rfl (run_tramp0 input)
      rfl deployAddress_not_precompile

/-- The body's own `JUMPDEST`, reached directly by the retargeted entry push. -/
private def gasSteps_tramp7Dest (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 1196)
      (headerEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp7DestPath rfl rfl
      (run_tramp7Dest input) rfl deployAddress_not_precompile

private def gasSteps_headerLoad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (headerEntryState input)
      (headerLoadedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka headerLoadPath rfl rfl (run_headerLoad input)
      rfl deployAddress_not_precompile

private def gasSteps_headerCheck (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (headerLoadedState input) (headerState input) := by
  exact
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka headerModulusCheckPath rfl rfl
      (run_headerModulusCheck input hvalid) rfl deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka headerExponentCheckPath rfl rfl
      (run_headerExponentCheck input hvalid) rfl deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka headerBaseCheckPath rfl rfl
      (run_headerBaseCheck input hvalid) rfl deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka headerCheckOrPath rfl rfl
      (run_headerCheckOr input) rfl deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka headerCheckIsZeroPath rfl rfl
      (run_headerCheckIsZero input) rfl deployAddress_not_precompile).trans <|
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka headerCheckJumpPath rfl rfl
      (run_headerCheckJump input) rfl deployAddress_not_precompile

@[simp] private theorem gasSteps_tramp0_cost (input : ByteArray) :
    (gasSteps_tramp0 input).cost = 11 := by rfl

@[simp] private theorem gasSteps_tramp7Dest_cost (input : ByteArray) :
    (gasSteps_tramp7Dest input).cost = 1 := by rfl

@[simp] private theorem gasSteps_headerLoad_cost (input : ByteArray) :
    (gasSteps_headerLoad input).cost = 17 := by rfl

@[simp] private theorem gasSteps_headerCheck_cost
    (input : ByteArray) (hvalid : ValidInput input) :
    (gasSteps_headerCheck input hvalid).cost = 49 := by rfl

/-- Header parsing as a gas-parametric relational trace. -/
def gasSteps_header (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (headerState input) := by
  exact (gasSteps_tramp0 input).trans <|
    (gasSteps_tramp7Dest input).trans <|
    (gasSteps_headerLoad input).trans (gasSteps_headerCheck input hvalid)

/-- Exact, input-independent gas used by the single retargeted entry hop and
the three successful EIP-7823 size checks. -/
theorem gasSteps_header_cost (input : ByteArray) (hvalid : ValidInput input) :
    (gasSteps_header input hvalid).cost = 78 := by
  simp [gasSteps_header]


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
