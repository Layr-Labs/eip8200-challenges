import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoopGuard
set_option warningAsError true
set_option maxRecDepth 160000
set_option maxHeartbeats 16000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open EvmSemantics.EVM
open Word

def bitFinishTailHeadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Word.opAt 464 .JUMPDEST, Word.opAt 465 .POP,
   Word.opAt 466 .POP, Word.opAt 467 .POP]

def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Word.pushAt 468 1 1, Word.opAt 469 .ADD,
   Word.pushAt 470 2 537, Word.opAt 471 .JUMP]

def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 561
    stack := [UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1182] ++ callerRest input }

@[simp] private theorem exitPCs (i : Nat)
    (hi : 464 ≤ i) (hii : i ≤ 485) :
    Artifact.submissionArtifact.instructionPC i =
      ([557,558,559,560,561,563,564,567,568,569,570,571,572,574,575,577,578,579,580,581,582,583] : List Nat)[i - 464]! := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 557).succ = UInt256.ofNat 558 := by decide
  have h657 : (UInt256.ofNat 558).succ = UInt256.ofNat 559 := by decide
  have h658 : (UInt256.ofNat 559).succ = UInt256.ofNat 560 := by decide
  have h659 : (UInt256.ofNat 560).succ = UInt256.ofNat 561 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath, Word.opAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState, bitFinishTailMidState, bitLoopState, bitTail, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, h656, h657, h658, h659]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
