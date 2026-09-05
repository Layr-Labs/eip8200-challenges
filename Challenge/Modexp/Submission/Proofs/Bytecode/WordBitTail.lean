import Challenge.Modexp.Submission.Proofs.Bytecode.WordBits
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# One-word MODEXP path: exponent-bit selection and back-edge

Split out of the original single-file `Word` module; the earlier certificate
blocks now live in `WordDefs` and `WordExp`.
-/
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

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
      bitProductState, bitSelectedState, bitLoopState, bitStep,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs]

def bitAdvanceHeadPath := bitAdvancePath.take 9
def bitAdvanceJumpPath := bitAdvancePath.drop 9

/-- Loop state reached just before the bit back-edge `PUSH2 606; JUMP`. -/
def bitAdvanceMidState (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer (j + 1) byte offset
      (bitStep input byte j acc base) base with pc := UInt256.ofNat 651 }

set_option linter.unusedSimpArgs false in
theorem run_bitAdvanceHead (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvanceHeadPath
      (bitSelectedState input outer j byte offset acc base) =
        some (bitAdvanceMidState input outer j byte offset acc base) := by
  have hsucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := j) (b := 1) (by omega : j + 1 < 2 ^ 256)
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitAdvanceHeadPath, bitAdvancePath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSelectedState, bitAdvanceMidState, bitLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      expPCs, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hj, hsucc', honeWord]

set_option linter.unusedSimpArgs false in
theorem run_bitAdvanceJump (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvanceJumpPath
      (bitAdvanceMidState input outer j byte offset acc base) =
        some (bitLoopState input outer (j + 1) byte offset
          (bitStep input byte j acc base) base) := by
  have h606 : (606 : UInt256).toNat = 606 := by decide
  have h606Word : (606 : UInt256) = UInt256.ofNat 606 := by decide
  simp (config := { maxSteps := 175000 })
    [bitAdvanceJumpPath, bitAdvancePath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitAdvanceMidState, bitLoopState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, expPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat, h606, h606Word, jump606]

theorem run_bitAdvance (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath
      (bitSelectedState input outer j byte offset acc base) =
        some (bitLoopState input outer (j + 1) byte offset
          (bitStep input byte j acc base) base) := by
  have hsplit : bitAdvancePath = bitAdvanceHeadPath ++ bitAdvanceJumpPath :=
    (List.take_append_drop 9 bitAdvancePath).symm
  have hrunning :
      (bitAdvanceMidState input outer j byte offset acc base).halt = .Running := rfl
  rw [hsplit]
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_bitAdvanceHead input outer j byte offset acc base hj) hrunning
    (run_bitAdvanceJump input outer j byte offset acc base)

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
