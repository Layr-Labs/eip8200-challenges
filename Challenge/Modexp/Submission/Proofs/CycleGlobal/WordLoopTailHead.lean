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
  [opAt 7620 .JUMPDEST,
   opAt 7621 .POP,
   opAt 7622 .POP,
   opAt 7623 .POP]
def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 7624 1 1,
   opAt 7625 .ADD,
   pushAt 7626 1 187,
   opAt 7627 .JUMP]
def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 9808
    stack := [UInt256.ofNat outer,acc,base,
      UInt256.ofNat (modulusValue input),UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input),UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96,UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input),UInt256.ofNat 1186]++callerRest input }
@[simp] private theorem exitPCs (i : Nat) (hi : 7620 ≤ i) (hii : i ≤ 7641) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([9804,9805,9806,9807,9808,9810,9811,9813,9814,9815,9816,9817,9818,9820,9821,9823,9824,9825,9826,9827,9828,9829] : List Nat)[i - 7620]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 9804).succ = UInt256.ofNat 9805 := by decide
  have h657 : (UInt256.ofNat 9805).succ = UInt256.ofNat 9806 := by decide
  have h658 : (UInt256.ofNat 9806).succ = UInt256.ofNat 9807 := by decide
  have h659 : (UInt256.ofNat 9807).succ = UInt256.ofNat 9808 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath,Word.opAt,Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState,bitFinishTailMidState,bitLoopState,bitTail,nonzeroState,
      callerRest,Dispatch.wordEntryState,Main.headerState,initialState,
      exitPCs,h656,h657,h658,h659]
end CycleSubmission.Global.WordLoops
