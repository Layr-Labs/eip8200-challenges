import Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatchCheck
import Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatchTail
import Challenge.EvmProof.Meter
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

private def gasSteps_bigTailFrame (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigCheckedState input)
      (bigTailFrameState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka bigTailFramePath rfl rfl
      (run_bigTailFrame input) rfl deployAddress_not_precompile

private def gasSteps_bigTailArgs (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigTailFrameState input)
      (bigTailArgsState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka bigTailArgsPath rfl rfl
      (run_bigTailArgs input) rfl deployAddress_not_precompile

private def gasSteps_bigTailJump (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigTailArgsState input) (bigEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka bigTailJumpPath rfl rfl
      (run_bigTailJump input) rfl deployAddress_not_precompile

def gasSteps_bigTail (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigCheckedState input) (bigEntryState input) :=
  (gasSteps_bigTailFrame input).trans <|
    (gasSteps_bigTailArgs input).trans (gasSteps_bigTailJump input)

private def gasSteps_bigCheckExp (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordDispatchState input)
      (bigExpOffsetState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka bigCheckExpPath rfl rfl
      (run_bigCheckExp input hvalid) rfl deployAddress_not_precompile

private def gasSteps_bigCheckMod (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (bigExpOffsetState input)
      (bigOffsetsState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka bigCheckModPath rfl rfl
      (run_bigCheckMod input hvalid) rfl deployAddress_not_precompile

private def gasSteps_bigCheckCompare (input : ByteArray)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (bigOffsetsState input)
      (bigComparedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka bigCheckComparePath rfl rfl
      (run_bigCheckCompare input hvalid hbig) rfl deployAddress_not_precompile

private def gasSteps_bigCheckJump (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigComparedState input)
      (bigCheckedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka bigCheckJumpPath rfl rfl
      (run_bigCheckJump input) rfl deployAddress_not_precompile

def gasSteps_bigCheck (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordDispatchState input)
      (bigCheckedState input) :=
  (gasSteps_bigCheckExp input hvalid).trans <|
    (gasSteps_bigCheckMod input hvalid).trans <|
      (gasSteps_bigCheckCompare input hvalid hbig).trans
        (gasSteps_bigCheckJump input)

def gasSteps_bigJump (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (Dispatch.wordDispatchState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka Dispatch.wordJumpPath rfl rfl
      (Dispatch.run_wordJump input hvalid hpositive) rfl
      deployAddress_not_precompile

def gasSteps_bigEntry (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Main.headerState input) (bigEntryState input) :=
  (gasSteps_bigJump input hvalid hpositive).trans <|
    (gasSteps_bigCheck input hvalid hbig).trans (gasSteps_bigTail input)

end Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch
