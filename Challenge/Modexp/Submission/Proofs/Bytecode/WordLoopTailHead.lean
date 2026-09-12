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
  [Word.opAt 502 .JUMPDEST, Word.opAt 503 .POP,
   Word.opAt 504 .POP, Word.opAt 505 .POP]

def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Word.pushAt 506 1 1, Word.opAt 507 .ADD,
   Word.pushAt 508 2 590, Word.opAt 509 .JUMP]

def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 614
    stack := [UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1186] ++ callerRest input }

@[simp] private theorem exitPCs (i : Nat)
    (hi : 502 ≤ i) (hii : i ≤ 523) :
    Artifact.submissionArtifact.instructionPC i =
      ([610,611,612,613,614,616,617,620,621,622,623,624,625,627,628,630,631,632,633,634,635,636] : List Nat)[i - 502]! := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 610).succ = UInt256.ofNat 611 := by decide
  have h657 : (UInt256.ofNat 611).succ = UInt256.ofNat 612 := by decide
  have h658 : (UInt256.ofNat 612).succ = UInt256.ofNat 613 := by decide
  have h659 : (UInt256.ofNat 613).succ = UInt256.ofNat 614 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath, Word.opAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState, bitFinishTailMidState, bitLoopState, bitTail, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, h656, h657, h658, h659]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
