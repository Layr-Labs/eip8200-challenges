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
    (hi : 518 ≤ i) (hii : i ≤ 539) :
    Artifact.submissionArtifact.instructionPC i =
      ([628,629,630,631,632,634,635,638,639,640,641,642,643,645,646,648,649,650,651,652,653,654] : List Nat)[i - 518]! := by
  interval_cases i <;> decide

@[simp] private theorem jump589 :
    Decode.isValidJumpDest submissionBytecode 567 = true :=
  Artifact.isValidJumpDest_index 466 (by rfl)

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
  have h589 : (567 : UInt256).toNat = 567 := by decide
  have h589Word : (567 : UInt256) = UInt256.ofNat 567 := by decide
  simp (config := { maxSteps := 125000 })
    [bitFinishTailFinishPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishTailMidState, bitLoopState, bitTail, expLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      hsucc, hincLeft, honeWord, h589, h589Word, jump589]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
