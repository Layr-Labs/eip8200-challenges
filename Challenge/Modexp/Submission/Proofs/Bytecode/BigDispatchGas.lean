import Challenge.Modexp.Submission.Proofs.Bytecode.MemoCert
import Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatchCheck
import Challenge.EvmProof.Meter
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

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

private theorem gasSteps_bigCheckExp_cost (input : ByteArray)
    (hvalid : ValidInput input) :
    (gasSteps_bigCheckExp input hvalid).cost = 10 := by rfl

private theorem gasSteps_bigCheckMod_cost (input : ByteArray)
    (hvalid : ValidInput input) :
    (gasSteps_bigCheckMod input hvalid).cost = 9 := by rfl

private theorem gasSteps_bigCheckCompare_cost (input : ByteArray)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input) :
    (gasSteps_bigCheckCompare input hvalid hbig).cost = 9 := by rfl

private theorem gasSteps_bigCheckJump_cost (input : ByteArray) :
    (gasSteps_bigCheckJump input).cost = 13 := by rfl

def gasSteps_bigCheck (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordDispatchState input)
      (bigCheckedState input) :=
  (gasSteps_bigCheckExp input hvalid).trans <|
    (gasSteps_bigCheckMod input hvalid).trans <|
      (gasSteps_bigCheckCompare input hvalid hbig).trans
        (gasSteps_bigCheckJump input)

theorem gasSteps_bigCheck_cost (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    (gasSteps_bigCheck input hvalid hbig).cost = 41 := by
  simp [gasSteps_bigCheck, gasSteps_bigCheckExp_cost,
    gasSteps_bigCheckMod_cost, gasSteps_bigCheckCompare_cost,
    gasSteps_bigCheckJump_cost]

/-- A modulus wider than 32 bytes is never recognised by the appended block, so
the wide route always takes its miss exit. -/
theorem bigMiss (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) : MemoLogic.guardDiff input ≠ 0 := by
  intro h
  obtain ⟨hms, -, -, -⟩ :=
    MemoCert.pins input hvalid ((MemoLogic.guardDiff_eq_zero_iff input).mp h)
  omega

def gasSteps_bigJump (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input)
    (hmiss : MemoLogic.guardDiff input ≠ 0) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (Dispatch.wordDispatchState input) :=
  (Dispatch.gasSteps_guardEnter input hvalid hpositive).trans
    (Dispatch.gasSteps_guardMiss input hmiss)

theorem gasSteps_bigJump_cost (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input)
    (hmiss : MemoLogic.guardDiff input ≠ 0) :
    (gasSteps_bigJump input hvalid hpositive hmiss).cost = 75 := by
  simp [gasSteps_bigJump]

/-- From the header state to the fallback entry: the dispatcher's jump and its
size check.  No trampoline frame is built any more. -/
def gasSteps_bigEntry (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Main.headerState input) (bigEntryState input) :=
  (gasSteps_bigJump input hvalid hpositive (bigMiss input hvalid hbig)).trans
    (gasSteps_bigCheck input hvalid hbig)

theorem gasSteps_bigEntry_cost (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hbig : 32 < modulusSize input) :
    (gasSteps_bigEntry input hvalid hpositive hbig).cost = 116 := by
  simp [gasSteps_bigEntry, gasSteps_bigJump_cost, gasSteps_bigCheck_cost]

end Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch
