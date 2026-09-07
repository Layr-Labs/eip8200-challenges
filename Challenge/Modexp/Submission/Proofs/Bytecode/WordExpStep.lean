import Challenge.Modexp.Submission.Proofs.Bytecode.Word
import Challenge.Modexp.Submission.Proofs.Bytecode.WordBitSquare
import Challenge.Modexp.Submission.Proofs.Bytecode.WordBitMaskProduct
import Challenge.Modexp.Submission.Proofs.Bytecode.WordBitChooseAdvance

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

/- Checked in `WordBitSquare`. -/
/-
set_option linter.unusedSimpArgs false in
theorem run_bitSquare (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitSquarePath
      (bitDecodedState input outer j byte offset acc base) =
        some (bitSquaredState input outer j byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitSquarePath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitDecodedState, bitSquaredState, bitLoopState, bitTail,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, stepPCs, List.exchange]

-/

/- Checked in the two bounded bit-step leaf modules. -/
/-
set_option linter.unusedSimpArgs false in
theorem run_bitMask (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitMaskPath
      (bitSquaredState input outer j byte offset acc base) =
        some (bitMaskedState input outer j byte offset acc base) := by
  have hzeroRaw : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 125000 })
    [bitMaskPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState, bitMaskedState, bitLoopState, bitTail,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, hzeroRaw]

set_option linter.unusedSimpArgs false in
theorem run_bitProduct (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitProductPath
      (bitMaskedState input outer j byte offset acc base) =
        some (bitProductState input outer j byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitProductPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitMaskedState, bitProductState, bitLoopState, bitTail,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs]

set_option linter.unusedSimpArgs false in
theorem run_bitChoose (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitChoosePath
      (bitProductState input outer j byte offset acc base) =
        some (bitSelectedState input outer j byte offset acc base) := by
  simp (config := { maxSteps := 150000 })
    [bitChoosePath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitProductState, bitSelectedState, bitLoopState, bitTail, bitStep,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs]

set_option linter.unusedSimpArgs false in
theorem run_bitAdvance (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath
      (bitSelectedState input outer j byte offset acc base) =
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
    [bitAdvancePath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSelectedState, bitLoopState, bitTail, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      expPCs, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hj, hsucc', hincLeft, h606, h606Word, honeWord, jump606]

-/

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
