import Challenge.Modexp.Submission.Proofs.Bytecode.WordExp
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# One-word MODEXP path: exponent-bit loop body

Split out of the original single-file `Word` module; the earlier certificate
blocks now live in `WordDefs` and `WordExp`.
-/
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

set_option linter.unusedSimpArgs false in
theorem run_bitGuard (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitGuardPath
      (bitLoopState input outer j byte offset acc base) =
        some (bitGuardState input outer j byte offset acc base) := by
  have hj256 : j < 2 ^ 256 := by omega
  have hjmod : j % 2 ^ 256 = j := Nat.mod_eq_of_lt hj256
  have h8mod : 8 % 2 ^ 256 = 8 := by norm_num
  have hjlt : j % 2 ^ 256 < 8 % 2 ^ 256 := by
    rw [hjmod, h8mod]
    exact hj
  have hjltLiteral :
      j %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        8 %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hjlt ⊢
    exact hjlt
  have hcondLiteral :
      (if j %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
          8 %
          115792089237316195423570985008687907853269984665640564039457584007913129639936
        then UInt256.ofNat 1 else UInt256.ofNat 0).isZero.toNat = 0 := by
    rw [if_pos hjltLiteral]
    decide
  have h616 : (616 : UInt256).toNat = 616 := by decide
  have h8 : (8 : UInt256).toNat = 8 := by decide
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [bitGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitLoopState, bitGuardState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, expPCs,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      hj, hj256, hjmod, h8mod, hjlt, hjltLiteral, hcondLiteral,
      h8, honeIsZero, h616]

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
      bitGuardState, bitDecodedState, bitLoopState, exponentBit,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt, hj, hsub, hshift, hbyte, h7Word, h1Word]

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
      bitDecodedState, bitSquaredState, bitLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, List.exchange]

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
      bitSquaredState, bitMaskedState, bitLoopState,
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
      bitMaskedState, bitProductState, bitLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs]


end Challenge.Modexp.Submission.Proofs.Bytecode.Word
