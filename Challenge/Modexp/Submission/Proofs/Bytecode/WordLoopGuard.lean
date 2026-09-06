import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoopGuardJump
set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open Word

theorem run_bitFinishGuard (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitGuardPath
      (bitLoopState input outer 8 byte offset acc base) =
        some (bitFinishDispatchState input outer byte offset acc base) := by
  change Challenge.EvmProof.Stepper.runLocatedBlock
      (bitFinishGuardHeadPath ++ bitFinishGuardPushPath ++ bitFinishGuardJumpPath)
      (bitLoopState input outer 8 byte offset acc base) = _
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    bitFinishGuardHeadPath (bitFinishGuardPushPath ++ bitFinishGuardJumpPath)
    (bitLoopState input outer 8 byte offset acc base)
    (bitFinishComparedState input outer byte offset acc base)
    (bitFinishDispatchState input outer byte offset acc base)
    (run_bitFinishGuardHead input outer byte offset acc base) rfl
    (Challenge.EvmProof.Stepper.runLocatedBlock_append
      bitFinishGuardPushPath bitFinishGuardJumpPath
      (bitFinishComparedState input outer byte offset acc base)
      (bitFinishJumpState input outer byte offset acc base)
      (bitFinishDispatchState input outer byte offset acc base)
      (run_bitFinishGuardPush input outer byte offset acc base) rfl
      (run_bitFinishGuardJump input outer byte offset acc base))

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
