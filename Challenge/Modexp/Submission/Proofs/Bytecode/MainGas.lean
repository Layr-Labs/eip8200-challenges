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

private def gasSteps_tramp1 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 14)
      (trampolineState input 53) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp1Path rfl rfl (run_tramp1 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp2 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 53)
      (trampolineState input 99) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp2Path rfl rfl (run_tramp2 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp3 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 99)
      (trampolineState input 305) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp3Path rfl rfl (run_tramp3 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp4 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 305)
      (trampolineState input 434) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp4Path rfl rfl (run_tramp4 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp5 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 434)
      (trampolineState input 512) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp5Path rfl rfl (run_tramp5 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp6 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 512)
      (trampolineState input 699) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp6Path rfl rfl (run_tramp6 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp7 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 699)
      (headerEntryState input) := by
  apply Challenge.EvmProof.GasSteps.trans
  · exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka tramp7JumpPath rfl rfl
        (run_tramp7Jump input) rfl deployAddress_not_precompile
  · exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
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

def gasSteps_header (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (headerState input) := by
  exact (gasSteps_tramp0 input).trans <|
    (gasSteps_tramp7Dest input).trans <|
    (gasSteps_headerLoad input).trans (gasSteps_headerCheck input hvalid)

end Challenge.Modexp.Submission.Proofs.Bytecode.Main
