import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordLoopTailHead
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

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

@[simp] private theorem exitPCs (i : Nat) (hi : 3048 ≤ i) (hii : i ≤ 3069) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3983, 3984, 3985, 3986, 3987, 3989, 3990, 3992, 3993, 3994, 3995, 3996, 3997, 3999, 4000, 4002, 4003, 4004, 4005, 4006, 4007, 4008] : List Nat)[i - 3048]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] private theorem jump589 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 187 = true :=
  CycleSubmission.Global.Binding.jumpDest 119 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailFinish (input : ByteArray) (outer : Nat)
    (acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailFinishPath
      (bitFinishTailMidState input outer acc base) =
        some (expLoopState input (outer + 1) acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsucc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := outer) (b := 1) (by omega : outer + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat outer =
      UInt256.ofNat (outer + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hsucc
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h589 : (187 : UInt256).toNat = 187 := by decide
  have h589Word : (187 : UInt256) = UInt256.ofNat 187 := by decide
  simp (config := { maxSteps := 125000 })
    [bitFinishTailFinishPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishTailMidState, bitLoopState, bitTail, expLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      hsucc, hincLeft, honeWord, h589, h589Word, jump589]

end CycleSubmission.Global.WordLoops
