import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoopGuardPush
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open EvmSemantics.EVM
open Word

@[simp] private theorem jump655 :
    Decode.isValidJumpDest submissionBytecode 655 = true :=
  Artifact.isValidJumpDest_index 523 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_bitFinishGuardJump (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishGuardJumpPath
      (bitFinishJumpState input outer byte offset acc base) =
        some (bitFinishDispatchState input outer byte offset acc base) := by
  have hone : (UInt256.ofNat 1).toNat = 1 := by decide
  have h655 : (UInt256.ofNat 655).toNat = 655 := by decide
  simp (config := { maxSteps := 75000 })
    [bitFinishGuardJumpPath, Word.opAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishJumpState, bitFinishComparedState, bitFinishDispatchState,
      bitLoopState, nonzeroState, callerRest, Dispatch.wordEntryState,
      Main.headerState, initialState, Word.expPCs, UInt256.isTrue,
      hone, h655, jump655]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
