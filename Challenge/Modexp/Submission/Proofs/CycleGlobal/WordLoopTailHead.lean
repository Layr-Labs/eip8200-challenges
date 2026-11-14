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
  [opAt 7928 .JUMPDEST,
   opAt 7929 .POP,
   opAt 7930 .POP,
   opAt 7931 .POP]
def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 7932 1 1,
   opAt 7933 .ADD,
   pushAt 7934 1 187,
   opAt 7935 .JUMP]
def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 10342
    stack := [UInt256.ofNat outer,acc,base,
      UInt256.ofNat (modulusValue input),UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input),UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96,UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input),UInt256.ofNat 1186]++callerRest input }
@[simp] private theorem exitPCs (i : Nat) (hi : 7928 ≤ i) (hii : i ≤ 7949) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10338,10339,10340,10341,10342,10344,10345,10347,10348,10349,10350,10351,10352,10354,10355,10357,10358,10359,10360,10361,10362,10363] : List Nat)[i - 7928]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 10338).succ = UInt256.ofNat 10339 := by decide
  have h657 : (UInt256.ofNat 10339).succ = UInt256.ofNat 10340 := by decide
  have h658 : (UInt256.ofNat 10340).succ = UInt256.ofNat 10341 := by decide
  have h659 : (UInt256.ofNat 10341).succ = UInt256.ofNat 10342 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath,Word.opAt,Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState,bitFinishTailMidState,bitLoopState,bitTail,nonzeroState,
      callerRest,Dispatch.wordEntryState,Main.headerState,initialState,
      exitPCs,h656,h657,h658,h659]
end CycleSubmission.Global.WordLoops
