import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoopTailHead
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open EvmSemantics.EVM
open Word

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

@[simp] private theorem exitPCs (i : Nat)
    (hi : 141 ≤ i) (hii : i ≤ 162) :
    Artifact.submissionArtifact.instructionPC i =
      ([210,211,212,213,214,216,217,219,220,221,222,223,224,226,227,229,230,231,232,233,234,235] : List Nat)[i - 141]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] private theorem jump589 :
    Decode.isValidJumpDest submissionBytecode 191 = true :=
  Artifact.isValidJumpDest_index 125 (by rfl)

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
  have h589 : (191 : UInt256).toNat = 191 := by decide
  have h589Word : (191 : UInt256) = UInt256.ofNat 191 := by decide
  simp (config := { maxSteps := 125000 })
    [bitFinishTailFinishPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishTailMidState, bitLoopState, bitTail, expLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      hsucc, hincLeft, honeWord, h589, h589Word, jump589]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
