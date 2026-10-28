import Challenge.Ripemd160.Submission.Local20261028.RecDispatch0
import Challenge.Ripemd160.Submission.Local20261028.RecDispatch31
import Challenge.Ripemd160.Submission.Local20261028.RecDispatch32
import Challenge.Ripemd160.Submission.Local20261028.RecDispatch55
import Challenge.Ripemd160.Submission.Local20261028.RecDispatch56
import Challenge.Ripemd160.Submission.Local20261028.RecDispatch63
import Challenge.Ripemd160.Submission.Local20261028.RecDispatch64
import Challenge.Ripemd160.Submission.Local20261028.RecDispatch65
import Challenge.Ripemd160.Submission.Local20261028.RecDispatch119
import Challenge.Ripemd160.Submission.Local20261028.RecDispatch120
import Challenge.Ripemd160.Submission.Local20261028.RecDispatch128
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

theorem valid_arm1 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 8180 = true :=
  valid_at 6169 8180 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_short1 (input : ByteArray) (h : input.size = 1) :
    GasSteps (Control.DirectGuard.guardEntry input) (atState (base input) 8180 []) := by
  have hs := Control.Patterned128Entry.shortSource_eq input 1 8180 h (by decide)
  have hn : (Control.Patterned128Entry.shortSource input).toNat = 8180 := by rw [hs]; rfl
  have g := Control.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_arm1)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

/-- The empty input reaches the shared empty-digest arm through its trampoline. -/
def gasSteps_to_empty (input : ByteArray) (hz : input.size = 0) :
    GasSteps (Control.DirectGuard.guardEntry input) (Control.AbcArm.emptyEntry input) :=
  (gasSteps_short0 input hz).trans (gasSteps_tramp0 input)

/-- Every allowed size other than 1000 returns the reference digest. -/
theorem from_entry (input : ByteArray) (hfit : CalldataFits input)
    (hn : RecognitionAccumulator.Allowed input.size) (h1000 : input.size ≠ 1000)
    (hguard : GasSteps (initialState Control.submissionBytecode input 0)
      (Control.DirectGuard.guardEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState Control.submissionBytecode input gas) (.returned (spec input)) := by
  have hn' := hn
  unfold RecognitionAccumulator.Allowed at hn'
  rcases hn' with h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have g := hguard.trans ((gasSteps_short1 input h).trans (Each.gasSteps_arm1 input))
    exact Finish.arm_correct input hfit 1 (h ▸ hn) h 8244 g
      (Finish.finish_gasSteps input 1 8244 Finish.finishSite0 Finish.finishSite0_pc)
  · have g := hguard.trans (((gasSteps_short31 input h).trans (gasSteps_tramp31 input)).trans (Each.gasSteps_arm31 input))
    exact Finish.arm_correct input hfit 31 (h ▸ hn) h 8825 g
      (Finish.finish_gasSteps input 31 8825 Finish.finishSite1 Finish.finishSite1_pc)
  · have g := hguard.trans (((gasSteps_short32 input h).trans (gasSteps_tramp32 input)).trans (Each.gasSteps_arm32 input))
    exact Finish.arm_correct input hfit 32 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 32 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short55 input h).trans (gasSteps_tramp55 input)).trans (Each.gasSteps_arm55 input))
    exact Finish.arm_correct input hfit 55 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 55 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short56 input h).trans (gasSteps_tramp56 input)).trans (Each.gasSteps_arm56 input))
    exact Finish.arm_correct input hfit 56 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 56 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short63 input h).trans (gasSteps_tramp63 input)).trans (Each.gasSteps_arm63 input))
    exact Finish.arm_correct input hfit 63 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 63 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short64 input h).trans (gasSteps_tramp64 input)).trans (Each.gasSteps_arm64 input))
    exact Finish.arm_correct input hfit 64 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 64 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short65 input h).trans (gasSteps_tramp65 input)).trans (Each.gasSteps_arm65 input))
    exact Finish.arm_correct input hfit 65 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 65 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short119 input h).trans (gasSteps_tramp119 input)).trans (Each.gasSteps_arm119 input))
    exact Finish.arm_correct input hfit 119 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 119 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short120 input h).trans (gasSteps_tramp120 input)).trans (Each.gasSteps_arm120 input))
    exact Finish.arm_correct input hfit 120 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 120 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short128 input h).trans (gasSteps_tramp128 input)).trans (Each.gasSteps_arm128 input))
    exact Finish.arm_correct input hfit 128 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 128 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans ((GasSteps.cast (Control.Patterned128Entry.gasSteps_256 input hfit h
        (valid_at 6399 9302 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))) rfl rfl).trans (Each.gasSteps_arm256 input))
    exact Finish.arm_correct input hfit 256 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 256 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · exact Long.correct376 input hfit h (hguard.trans (GasSteps.cast
      (Control.Patterned128Entry.gasSteps_376 input hfit h
        (valid_at 6406 9331 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))) rfl rfl))
  · exact absurd h h1000

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Dispatch
