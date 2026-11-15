import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordLoopGuard
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
namespace CycleSubmission.Global.WordLoops
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics
open EvmSemantics.EVM
open Word
def bitFinishTailHeadPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 6347 .JUMPDEST,
   opAt 6348 .POP,
   opAt 6349 .POP,
   opAt 6350 .POP]
def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 6351 1 1,
   opAt 6352 .ADD,
   pushAt 6353 1 152,
   opAt 6354 .JUMP]
def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 8437
    stack := [UInt256.ofNat outer,acc,base,
      UInt256.ofNat (modulusValue input),UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input),UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96,UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input),UInt256.ofNat 1186]++callerRest input }
@[simp] private theorem exitPCs (i : Nat) (hi : 6347 ≤ i) (hii : i ≤ 6354) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([8433,8434,8435,8436,8437,8439,8440,8442] : List Nat)[i - 6347]! := by
  interval_cases i <;>
    exact CycleSubmission.PCCertificate.selectedPC _ (by decide)
@[simp] private theorem exitPCs_part1 (i : Nat) (hi : 8203 ≤ i) (hii : i ≤ 8216) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10885,10886,10887,10888,10889,10891,10892,10894,10895,10896,10897,10898,10899,10900] : List Nat)[i - 8203]! := by
  interval_cases i <;>
    exact CycleSubmission.PCCertificate.selectedPC _ (by decide)
set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 8433).succ = UInt256.ofNat 8434 := by decide
  have h657 : (UInt256.ofNat 8434).succ = UInt256.ofNat 8435 := by decide
  have h658 : (UInt256.ofNat 8435).succ = UInt256.ofNat 8436 := by decide
  have h659 : (UInt256.ofNat 8436).succ = UInt256.ofNat 8437 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath,Word.opAt,Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState,bitFinishTailMidState,bitLoopState,bitTail,nonzeroState,
      callerRest,Dispatch.wordEntryState,Main.headerState,initialState,
      exitPCs,h656,h657,h658,h659]
end CycleSubmission.Global.WordLoops
