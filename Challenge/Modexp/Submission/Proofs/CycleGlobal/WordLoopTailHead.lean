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
  [opAt 3043 .JUMPDEST,
   opAt 3044 .POP,
   opAt 3045 .POP,
   opAt 3046 .POP]

def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 3047 1 1,
   opAt 3048 .ADD,
   pushAt 3049 1 194,
   opAt 3050 .JUMP]

def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 4012
    stack := [UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1186] ++ callerRest input }

@[simp] private theorem exitPCs (i : Nat) (hi : 3043 ≤ i) (hii : i ≤ 3064) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([4008, 4009, 4010, 4011, 4012, 4014, 4015, 4017, 4018, 4019, 4020, 4021, 4022, 4024, 4025, 4027, 4028, 4029, 4030, 4031, 4032, 4033] : List Nat)[i - 3043]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 4008).succ = UInt256.ofNat 4009 := by decide
  have h657 : (UInt256.ofNat 4009).succ = UInt256.ofNat 4010 := by decide
  have h658 : (UInt256.ofNat 4010).succ = UInt256.ofNat 4011 := by decide
  have h659 : (UInt256.ofNat 4011).succ = UInt256.ofNat 4012 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath, Word.opAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState, bitFinishTailMidState, bitLoopState, bitTail, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, h656, h657, h658, h659]

end CycleSubmission.Global.WordLoops
