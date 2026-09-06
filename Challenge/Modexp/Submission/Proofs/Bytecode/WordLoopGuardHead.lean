import Challenge.Modexp.Submission.Proofs.Bytecode.WordExpRuns
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open EvmSemantics.EVM
open Word

def bitFinishGuardHeadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Word.opAt 484 .JUMPDEST, Word.opAt 485 (.Dup ⟨0, by decide⟩),
   Word.pushAt 486 1 7, Word.opAt 487 .LT]

def bitFinishGuardPushPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Word.opAt 488 .JUMPDEST, Word.pushAt 489 2 655]

def bitFinishGuardJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Word.opAt 490 .JUMPI]

def bitFinishComparedState (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer 8 byte offset acc base with
    pc := UInt256.ofNat 611
    stack := UInt256.ofNat 1 ::
      (bitLoopState input outer 8 byte offset acc base).stack }

def bitFinishDispatchState (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer 8 byte offset acc base with pc := UInt256.ofNat 655 }

set_option linter.unusedSimpArgs false in
theorem run_bitFinishGuardHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishGuardHeadPath
      (bitLoopState input outer 8 byte offset acc base) =
        some (bitFinishComparedState input outer byte offset acc base) := by
  have h8 : (8 : UInt256).toNat = 8 := by decide
  have h7 : (7 : UInt256).toNat = 7 := by decide
  have hltLiteral :
      7 %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        8 %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num
  have h607 : (UInt256.ofNat 606).succ = UInt256.ofNat 607 := by decide
  have h608 : (UInt256.ofNat 607).succ = UInt256.ofNat 608 := by decide
  have h610 : UInt256.ofNat 608 + UInt256.ofNat 2 = UInt256.ofNat 610 := by decide
  have h611 : (UInt256.ofNat 610).succ = UInt256.ofNat 611 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishGuardHeadPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitLoopState, bitFinishComparedState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, Word.expPCs,
      UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      h8, h7, hltLiteral, h607, h608, h610, h611]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
