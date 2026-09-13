import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
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
  [Word.opAt 153 .JUMPDEST, Word.opAt 154 .POP,
   Word.opAt 155 .POP, Word.opAt 156 .POP]

def bitFinishTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Word.pushAt 157 1 1, Word.opAt 158 .ADD,
   Word.pushAt 159 1 205, Word.opAt 160 .JUMP]

def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { bitLoopState input outer 8 0 0 acc base with
    pc := UInt256.ofNat 228
    stack := [UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1186] ++ callerRest input }

@[simp] private theorem exitPCs (i : Nat)
    (hi : 153 ≤ i) (hii : i ≤ 174) :
    Artifact.submissionArtifact.instructionPC i =
      ([224,225,226,227,228,230,231,233,234,235,236,237,238,240,241,243,244,245,246,247,248,249] : List Nat)[i - 153]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  have h656 : (UInt256.ofNat 224).succ = UInt256.ofNat 225 := by decide
  have h657 : (UInt256.ofNat 225).succ = UInt256.ofNat 226 := by decide
  have h658 : (UInt256.ofNat 226).succ = UInt256.ofNat 227 := by decide
  have h659 : (UInt256.ofNat 227).succ = UInt256.ofNat 228 := by decide
  simp (config := { maxSteps := 100000 })
    [bitFinishTailHeadPath, Word.opAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState, bitFinishTailMidState, bitLoopState, bitTail, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, h656, h657, h658, h659]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
