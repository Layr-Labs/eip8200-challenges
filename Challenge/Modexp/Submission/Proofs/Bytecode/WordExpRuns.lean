import Challenge.Modexp.Submission.Proofs.Bytecode.Word
import Challenge.Modexp.Submission.Proofs.Bytecode.WordExpStep

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

set_option linter.unusedSimpArgs false in
theorem run_expGuard (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expGuardPath
      (expLoopState input i acc base) = some (expGuardState input i acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have he256 : exponentSize input < 2 ^ 256 := by omega
  have himod : i % 2 ^ 256 = i := Nat.mod_eq_of_lt hi256
  have hemod : exponentSize input % 2 ^ 256 = exponentSize input :=
    Nat.mod_eq_of_lt he256
  have hne : i ≠ exponentSize input := Nat.ne_of_lt hi
  have heq : UInt256.eq (UInt256.ofNat i) (UInt256.ofNat (exponentSize input)) =
      UInt256.ofNat 0 := by
    rw [UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, himod, hemod, if_neg hne]
  have h598 : (598 : UInt256).toNat = 598 := by decide
  have hzeroNat : (UInt256.ofNat 0).toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [expGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expLoopState, expGuardState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, expPCs,
      UInt256.isTrue, Challenge.EvmProof.Word.word_toNat_ofNat,
      hi, hi256, he256, himod, hemod, hne, heq, hzeroNat, h598]

set_option linter.unusedSimpArgs false in
theorem run_expLoad (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expLoadPath
      (expGuardState input i acc base) =
        some (bitLoopState input i 0 (byteWord input (expOffset input + i))
          (UInt256.ofNat (expOffset input + i)) acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hoff : expOffset input + i < 2 ^ 256 := by
    simp only [expOffset]
    omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := expOffset input) (b := i) hoff
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have hzeroRaw : ({ val := 0 } : UInt256) = 0 := by decide
  simp (config := { maxSteps := 175000 })
    [expLoadPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expGuardState, expLoopState, bitLoopState, bitTail, byteWord,
      Accessors.calldataByteValue,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      hoff, hadd, hzeroWord, hzeroRaw]

set_option linter.unusedSimpArgs false in
theorem run_bitDecode (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDecodePath
      (bitGuardState input outer j byte offset acc base) =
        some (bitDecodedState input outer j byte offset acc base) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : j ≤ 7)
    (by norm_num : 7 < 2 ^ 256)
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - j) byte.val.isLt (by omega)
  have hbyte : UInt256.ofNat byte.toNat = byte := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt byte.val.isLt
  have h7Word : (7 : UInt256) = UInt256.ofNat 7 := by decide
  have h1Word : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitDecodePath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitGuardState, bitDecodedState, bitLoopState, bitTail, exponentBit,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt, hj, hsub, hshift, hbyte, h7Word, h1Word]

/- The bit-update trace declarations are checked independently in
   `WordExpStep`; keeping them out of this elaboration bounds peak memory. -/
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
      initialState, expRunPCs, List.exchange]

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
      initialState, expRunPCs, hzeroRaw]

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
      initialState, expRunPCs]

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
      initialState, expRunPCs]

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
      expRunPCs, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hj, hsucc', hincLeft, h606, h606Word, honeWord, jump606]

-/

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
