import Challenge.Modexp.Submission.Proofs.Bytecode.Word

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

set_option linter.unusedSimpArgs false in
theorem run_bitAdvance_swap (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvanceSwapPath
      (bitSelectedState input outer j byte offset acc base) =
        some (bitAdvanceSwappedState input outer j byte offset acc base) := by
  simp (config := { maxSteps := 100000 })
    [bitAdvanceSwapPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSelectedState, bitAdvanceSwappedState, bitLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      expPCs, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_bitAdvance_drop (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvanceDropPath
      (bitAdvanceSwappedState input outer j byte offset acc base) =
        some (bitAdvanceDroppedState input outer j byte offset acc base) := by
  simp (config := { maxSteps := 100000 })
    [bitAdvanceDropPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitAdvanceSwappedState, bitAdvanceDroppedState, bitLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      expPCs]

set_option linter.unusedSimpArgs false in
theorem run_bitAdvance_finish (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvanceFinishPath
      (bitAdvanceDroppedState input outer j byte offset acc base) =
        some (bitLoopState input outer (j + 1) byte offset
          (bitStep input byte j acc base) base) := by
  have hsucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := j) (b := 1) (by omega : j + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat j =
      UInt256.ofNat (j + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hsucc'
  have h606 : (606 : UInt256).toNat = 606 := by decide
  have h606Word : (606 : UInt256) = UInt256.ofNat 606 := by decide
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitAdvanceFinishPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitAdvanceDroppedState, bitLoopState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      expPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hj, hsucc', hincLeft, h606, h606Word, honeWord, jump606]

theorem run_bitAdvance (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath
      (bitSelectedState input outer j byte offset acc base) =
        some (bitLoopState input outer (j + 1) byte offset
          (bitStep input byte j acc base) base) := by
  unfold bitAdvancePath
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    bitAdvanceSwapPath (bitAdvanceDropPath ++ bitAdvanceFinishPath)
    (bitSelectedState input outer j byte offset acc base)
    (bitAdvanceSwappedState input outer j byte offset acc base)
    (bitLoopState input outer (j + 1) byte offset
      (bitStep input byte j acc base) base)
    (run_bitAdvance_swap input outer j byte offset acc base) rfl
    (Challenge.EvmProof.Stepper.runLocatedBlock_append
      bitAdvanceDropPath bitAdvanceFinishPath
      (bitAdvanceSwappedState input outer j byte offset acc base)
      (bitAdvanceDroppedState input outer j byte offset acc base)
      (bitLoopState input outer (j + 1) byte offset
        (bitStep input byte j acc base) base)
      (run_bitAdvance_drop input outer j byte offset acc base) rfl
      (run_bitAdvance_finish input outer j byte offset acc base hj))

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
