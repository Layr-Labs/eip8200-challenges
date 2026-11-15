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
  [opAt 8065 .JUMPDEST,
   opAt 8066 .POP,
   opAt 8067 .POP,
   opAt 8068 .POP]
def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8069 1 1,
   opAt 8070 .ADD,
   pushAt 8071 1 152,
   opAt 8072 .JUMP]
def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 10687
    stack := [UInt256.ofNat outer,acc,base,
      UInt256.ofNat (modulusValue input),UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input),UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96,UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input),UInt256.ofNat 1186]++callerRest input }
@[simp] private theorem exitPCs (i : Nat) (hi : 8065 ≤ i) (hii : i ≤ 8086) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10683,10684,10685,10686,10687,10689,10690,10692,10693,10694,10695,10696,10697,10699,10700,10702,10703,10704,10705,10706,10707,10708] : List Nat)[i - 8065]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 10683).succ = UInt256.ofNat 10684 := by decide
  have h657 : (UInt256.ofNat 10684).succ = UInt256.ofNat 10685 := by decide
  have h658 : (UInt256.ofNat 10685).succ = UInt256.ofNat 10686 := by decide
  have h659 : (UInt256.ofNat 10686).succ = UInt256.ofNat 10687 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath,Word.opAt,Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState,bitFinishTailMidState,bitLoopState,bitTail,nonzeroState,
      callerRest,Dispatch.wordEntryState,Main.headerState,initialState,
      exitPCs,h656,h657,h658,h659]
end CycleSubmission.Global.WordLoops
