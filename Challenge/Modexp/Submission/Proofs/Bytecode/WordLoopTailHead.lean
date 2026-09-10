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
  [opAt 520 .JUMPDEST,
   opAt 521 .POP,
   opAt 522 .POP,
   opAt 523 .POP]

def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 524 1 1,
   opAt 525 .ADD,
   pushAt 526 2 588,
   opAt 527 .JUMP]

def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 654
    stack := [UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1262] ++ callerRest input }

@[simp] private theorem exitPCs (i : Nat)
    (hi : 520 ≤ i) (hii : i ≤ 544) :
    Artifact.submissionArtifact.instructionPC i =
      ([650,651,652,653,654,656,657,660,661,662,663,664,665,666,667,668,670,671,673,674,675,676,677,678,683] : List Nat)[i - 520]! := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 650).succ = UInt256.ofNat 651 := by decide
  have h657 : (UInt256.ofNat 651).succ = UInt256.ofNat 652 := by decide
  have h658 : (UInt256.ofNat 652).succ = UInt256.ofNat 653 := by decide
  have h659 : (UInt256.ofNat 653).succ = UInt256.ofNat 654 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath, Word.opAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState, bitFinishTailMidState, bitLoopState, bitTail, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, h656, h657, h658, h659]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
