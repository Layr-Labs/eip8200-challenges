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
  [opAt 7914 .JUMPDEST,
   opAt 7915 .POP,
   opAt 7916 .POP,
   opAt 7917 .POP]
def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 7918 1 1,
   opAt 7919 .ADD,
   pushAt 7920 1 187,
   opAt 7921 .JUMP]
def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 10464
    stack := [UInt256.ofNat outer,acc,base,
      UInt256.ofNat (modulusValue input),UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input),UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96,UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input),UInt256.ofNat 1186]++callerRest input }
@[simp] private theorem exitPCs (i : Nat) (hi : 7914 ≤ i) (hii : i ≤ 7935) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10460,10461,10462,10463,10464,10466,10467,10469,10470,10471,10472,10473,10474,10476,10477,10479,10480,10481,10482,10483,10484,10485] : List Nat)[i - 7914]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 10460).succ = UInt256.ofNat 10461 := by decide
  have h657 : (UInt256.ofNat 10461).succ = UInt256.ofNat 10462 := by decide
  have h658 : (UInt256.ofNat 10462).succ = UInt256.ofNat 10463 := by decide
  have h659 : (UInt256.ofNat 10463).succ = UInt256.ofNat 10464 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath,Word.opAt,Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState,bitFinishTailMidState,bitLoopState,bitTail,nonzeroState,
      callerRest,Dispatch.wordEntryState,Main.headerState,initialState,
      exitPCs,h656,h657,h658,h659]
end CycleSubmission.Global.WordLoops
