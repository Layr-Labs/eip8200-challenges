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

def tramp128Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (trampTemplate 5717) :=
  StackSiteBuilder.ofSlice (trampTemplate 5717) 3379 (by rfl)
    (by change 3379 + (trampTemplate 5717).length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 5717) (by decide)) (by decide)
theorem tramp128_pc : tramp128Site.startPC = UInt256.ofNat 4697 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3379) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp128 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 4697 = true :=
  valid_at 3379 4697 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp128 (input : ByteArray) :
    GasSteps (atState (base input) 4697 []) (atState (base input) 5717 []) :=
  RecognitionLift.gasSteps_of_raw tramp128Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp128_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 4697 5717 (by decide)
      (valid_at 3627 5717 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short128 (input : ByteArray) (h : input.size = 128) :
    GasSteps (Control.DirectGuard.guardEntry input) (atState (base input) 4697 []) := by
  have hs := Control.Patterned128Entry.shortSource_eq input 128 4697 h (by decide)
  have hn : (Control.Patterned128Entry.shortSource input).toNat = 4697 := by rw [hs]; rfl
  have g := Control.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp128)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Dispatch
