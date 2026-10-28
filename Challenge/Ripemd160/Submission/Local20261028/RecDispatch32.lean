import Challenge.Ripemd160.Submission.Local20261028.RecDispatchCommon
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

/-!
# Size dispatch into the compact arms

The short size table selects a three-byte trampoline (or the one-byte arm
directly); 256 and 376 bytes are matched by equality.  Every allowed size other
than 1000 reaches its arm and returns RIPEMD-160.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Dispatch
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate J2Moves ReverseLiteralRaw
open Arms.Scan

def tramp32Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (trampTemplate 8828) :=
  StackSiteBuilder.ofSlice (trampTemplate 8828) 6159 (by rfl)
    (by change 6159 + (trampTemplate 8828).length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 8828) (by decide)) (by decide)
theorem tramp32_pc : tramp32Site.startPC = UInt256.ofNat 8164 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6159) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp32 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 8164 = true :=
  valid_at 6159 8164 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp32 (input : ByteArray) :
    GasSteps (atState (base input) 8164 []) (atState (base input) 8828 []) :=
  RecognitionLift.gasSteps_of_raw tramp32Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp32_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8164 8828 (by decide)
      (valid_at 6318 8828 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short32 (input : ByteArray) (h : input.size = 32) :
    GasSteps (Control.DirectGuard.guardEntry input) (atState (base input) 8164 []) := by
  have hs := Control.Patterned128Entry.shortSource_eq input 32 8164 h (by decide)
  have hn : (Control.Patterned128Entry.shortSource input).toNat = 8164 := by rw [hs]; rfl
  have g := Control.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp32)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Dispatch
