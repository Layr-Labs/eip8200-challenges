import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoopGuard
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open EvmSemantics.EVM
open Word

def bitFinishTailHeadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Word.opAt 525 .JUMPDEST, Word.opAt 526 .POP,
   Word.opAt 527 .POP, Word.opAt 528 .POP]

def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Word.pushAt 529 1 1, Word.opAt 530 .ADD,
   Word.pushAt 531 2 589, Word.opAt 532 .JUMP]

def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 659
    stack := [UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1267] ++ callerRest input }

@[simp] private theorem exitPCs (i : Nat) (hi : 525 ≤ i) (hii : i ≤ 549) :
    Artifact.submissionArtifact.instructionPC i =
      [655,656,657,658,659,661,662,665,666,667,668,669,670,671,672,
       673,675,676,678,679,680,681,682,683,688][i - 525]! := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 655).succ = UInt256.ofNat 656 := by decide
  have h657 : (UInt256.ofNat 656).succ = UInt256.ofNat 657 := by decide
  have h658 : (UInt256.ofNat 657).succ = UInt256.ofNat 658 := by decide
  have h659 : (UInt256.ofNat 658).succ = UInt256.ofNat 659 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath, Word.opAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState, bitFinishTailMidState, bitLoopState, bitTail, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, h656, h657, h658, h659]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
