import Challenge.Ripemd160.Submission.Local20261028.RecDispatchCommon
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false


namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Dispatch
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate J2Moves ReverseLiteralRaw
open Arms.Scan

theorem valid_emptyArm : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 4690 = true :=
  valid_at 3383 4690 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_short0 (input : ByteArray) (h : input.size = 0) :
    GasSteps (Control.DirectGuard.guardEntry input) (atState (base input) 4690 []) := by
  have hs := Control.Patterned128Entry.shortSource_eq input 0 4690 h (by decide)
  have hn : (Control.Patterned128Entry.shortSource input).toNat = 4690 := by rw [hs]; rfl
  have g := Control.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_emptyArm)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Dispatch
