import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoopGuardHead
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open EvmSemantics.EVM
open Word

def bitFinishJumpState (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitFinishComparedState input outer byte offset acc base with
    pc := UInt256.ofNat 615
    stack := UInt256.ofNat 655 ::
      (bitFinishComparedState input outer byte offset acc base).stack }

set_option linter.unusedSimpArgs false in
theorem run_bitFinishGuardPush (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishGuardPushPath
      (bitFinishComparedState input outer byte offset acc base) =
        some (bitFinishJumpState input outer byte offset acc base) := by
  have h612 : (UInt256.ofNat 611).succ = UInt256.ofNat 612 := by decide
  have h615 : UInt256.ofNat 612 + UInt256.ofNat 3 = UInt256.ofNat 615 := by decide
  have h655 : (655 : UInt256) = UInt256.ofNat 655 := by decide
  simp (config := { maxSteps := 75000 })
    [bitFinishGuardPushPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishComparedState, bitFinishJumpState, bitLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      Word.expPCs, h612, h615, h655]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
