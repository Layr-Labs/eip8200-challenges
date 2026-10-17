import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdWideSeedRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! Bind the small compositional seed trace to the exact artifact.  In particular,
no simplifier unfolds the entire artifact while evaluating the memory warm-up. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState StackRoundTrace StackRoundTemplate

private def seed := ColdWideSeedRaw.template
private theorem seed_slice :
    (Artifact.submissionArtifact.instructions.drop 19).take seed.length = seed := by rfl
private theorem seed_pc : Artifact.submissionArtifact.instructionPC 19 = 33 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem seed_bounds :
    19 + seed.length ≤ Artifact.submissionArtifact.instructions.length := by
  change 19 + seed.length ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  decide
private theorem seed_wf : StackRoundData.TemplateWellFormed seed := by decide
private theorem seed_advances : ∀ i ∈ seed.dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  decide
private def seed_site : GenericRoundSite Artifact.submissionArtifact .Osaka seed :=
  StackSiteBuilder.ofSlice seed 19 seed_slice seed_bounds
    (by change submissionBytecode.size < 2 ^ 256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem seed_wf) (by decide)
private theorem seed_site_pc : seed_site.startPC = UInt256.ofNat 33 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 19) = _
  rw [seed_pc]

private theorem run_seed (input : ByteArray) :
    runInstrSeq seed (sizeMatched input) = some (loopState input 0) := by
  -- The cold seed preserves the shared state; collapse its redundant zero-memory
  -- update before simplifying projections, without unfolding the bytecode.
  have hcold : loopState input 0 =
      { initialState submissionBytecode input 0 with
        pc := UInt256.ofNat 9429
        stack := [equalityAcc input 0, referenceWord input] } := by rfl
  rw [hcold]
  simpa only [seed, sizeMatched, atPC, List.append_nil,
    Challenge.Ripemd160.initialState_calldata, Challenge.Ripemd160.initialState_stack,
    Word.literal_eq_ofNat] using
    ColdWideSeedRaw.run (initialState submissionBytecode input 0)
      (UInt256.ofNat 33) [] (by decide) rfl
      Artifact.validJumpDest_9429

/-- Without expanding memory, form the counter-free equality seed, and jump to the scanner. -/
def gasSteps_checkEntry (input : ByteArray) :
    GasSteps (sizeMatched input) (loopState input 0) :=
  RecognitionLift.gasSteps_of_raw seed_site _ _ (by rfl) (by rfl) (by rfl)
    deployAddress_not_precompile seed_site_pc.symm seed_advances (run_seed input)

#print axioms gasSteps_checkEntry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
