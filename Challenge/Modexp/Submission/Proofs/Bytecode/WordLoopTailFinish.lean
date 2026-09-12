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
    (hi : 502 ≤ i) (hii : i ≤ 523) :
    Artifact.submissionArtifact.instructionPC i =
      ([610,611,612,613,614,616,617,620,621,622,623,624,625,627,628,630,631,632,633,634,635,636] : List Nat)[i - 502]! := by
  interval_cases i <;> decide

@[simp] private theorem jump589 :
    Decode.isValidJumpDest submissionBytecode 590 = true :=
  Artifact.isValidJumpDest_index 486 (by rfl)

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
  have h589 : (590 : UInt256).toNat = 590 := by decide
  have h589Word : (590 : UInt256) = UInt256.ofNat 590 := by decide
  simp (config := { maxSteps := 125000 })
    [bitFinishTailFinishPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishTailMidState, bitLoopState, bitTail, expLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      hsucc, hincLeft, honeWord, h589, h589Word, jump589]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
