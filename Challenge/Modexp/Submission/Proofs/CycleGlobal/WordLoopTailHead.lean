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
  [opAt 2998 .JUMPDEST,
   opAt 2999 .POP,
   opAt 3000 .POP,
   opAt 3001 .POP]

def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 3002 1 1,
   opAt 3003 .ADD,
   pushAt 3004 1 187,
   opAt 3005 .JUMP]

def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 3832
    stack := [UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1186] ++ callerRest input }

@[simp] private theorem exitPCs (i : Nat) (hi : 2998 ≤ i) (hii : i ≤ 3019) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3828,3829,3830,3831,3832,3834,3835,3837,3838,3839,3840,3841,3842,3844,3845,3847,3848,3849,3850,3851,3852,3853] : List Nat)[i - 2998]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 3828).succ = UInt256.ofNat 3829 := by decide
  have h657 : (UInt256.ofNat 3829).succ = UInt256.ofNat 3830 := by decide
  have h658 : (UInt256.ofNat 3830).succ = UInt256.ofNat 3831 := by decide
  have h659 : (UInt256.ofNat 3831).succ = UInt256.ofNat 3832 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath, Word.opAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState, bitFinishTailMidState, bitLoopState, bitTail, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, h656, h657, h658, h659]

end CycleSubmission.Global.WordLoops
