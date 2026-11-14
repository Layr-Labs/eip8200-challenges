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
  [opAt 8001 .JUMPDEST,
   opAt 8002 .POP,
   opAt 8003 .POP,
   opAt 8004 .POP]
def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8005 1 1,
   opAt 8006 .ADD,
   pushAt 8007 1 187,
   opAt 8008 .JUMP]
def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 10412
    stack := [UInt256.ofNat outer,acc,base,
      UInt256.ofNat (modulusValue input),UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input),UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96,UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input),UInt256.ofNat 1186]++callerRest input }
@[simp] private theorem exitPCs (i : Nat) (hi : 8001 ≤ i) (hii : i ≤ 8022) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10408,10409,10410,10411,10412,10414,10415,10417,10418,10419,10420,10421,10422,10424,10425,10427,10428,10429,10430,10431,10432,10433] : List Nat)[i - 8001]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 10408).succ = UInt256.ofNat 10409 := by decide
  have h657 : (UInt256.ofNat 10409).succ = UInt256.ofNat 10410 := by decide
  have h658 : (UInt256.ofNat 10410).succ = UInt256.ofNat 10411 := by decide
  have h659 : (UInt256.ofNat 10411).succ = UInt256.ofNat 10412 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath,Word.opAt,Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState,bitFinishTailMidState,bitLoopState,bitTail,nonzeroState,
      callerRest,Dispatch.wordEntryState,Main.headerState,initialState,
      exitPCs,h656,h657,h658,h659]
end CycleSubmission.Global.WordLoops
