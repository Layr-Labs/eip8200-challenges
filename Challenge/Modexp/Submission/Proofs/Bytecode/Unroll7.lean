import Challenge.Modexp.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# Copy 7 of the unrolled exponent-bit body

The copy handles exponent bit 7.  Its six straight-line segments use the
fixed zero shift at instruction indices 2022 .. 2044 and bytes 3217 .. 3240.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7

open EvmSemantics
open EvmSemantics.EVM
open Word

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

def bitDecodePath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2022 (.Dup ⟨1, by decide⟩), pushAt 2023 1 1, opAt 2024 .AND]

def bitSquarePath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2025 (.Dup ⟨7, by decide⟩), opAt 2026 (.Dup ⟨6, by decide⟩),
   opAt 2027 (.Dup ⟨7, by decide⟩), opAt 2028 .MULMOD]

def bitMaskPath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2029 (.Dup ⟨1, by decide⟩), pushAt 2030 0 0, opAt 2031 .SUB]

def bitProductPath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2032 (.Dup ⟨9, by decide⟩), opAt 2033 (.Dup ⟨9, by decide⟩),
   opAt 2034 (.Dup ⟨3, by decide⟩), opAt 2035 .MULMOD]

def bitChoosePath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2036 (.Dup ⟨2, by decide⟩), opAt 2037 .XOR, opAt 2038 .AND,
   opAt 2039 (.Dup ⟨1, by decide⟩), opAt 2040 .XOR]

def bitAdvancePath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2041 (.Swap ⟨6, by decide⟩), opAt 2042 .POP, opAt 2043 .POP,
   opAt 2044 .POP]

set_option linter.unusedSimpArgs false in
theorem run_bitDecode (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDecodePath7
      (bitUnrollState input outer 7 byte offset acc base) =
        some (bitDecodedState7 input outer byte offset acc base) := by
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - 7) byte.val.isLt (by omega)
  have hbyte : UInt256.ofNat byte.toNat = byte := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt byte.val.isLt
  have hshiftByte : UInt256.shiftRight byte (UInt256.ofNat 0) = byte := by
    rw [← hbyte, hshift]
    simpa using hbyte
  have hland : UInt256.land (UInt256.ofNat 1) byte =
      UInt256.land byte (UInt256.ofNat 1) := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_land,
      Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]
  have h1Word : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitDecodePath7, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitUnrollState, bitDecodedState7, bitDecodedState, bitLoopState, bitPC,
      exponentBit, nonzeroState, callerRest, Dispatch.wordEntryState,
      Main.headerState, initialState, UnrollPCs.copyPC7,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hshiftByte, hland, h1Word]


set_option linter.unusedSimpArgs false in
theorem run_bitSquare (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitSquarePath7
      (bitDecodedState7 input outer byte offset acc base) =
        some (bitSquaredState7 input outer byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitSquarePath7, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitDecodedState7, bitDecodedState, bitSquaredState7, bitSquaredState,
      bitLoopState, bitPC, nonzeroState, callerRest, Dispatch.wordEntryState,
      Main.headerState, initialState, UnrollPCs.copyPC7, List.exchange]


set_option linter.unusedSimpArgs false in
theorem run_bitMask (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitMaskPath7
      (bitSquaredState7 input outer byte offset acc base) =
        some (bitMaskedState7 input outer byte offset acc base) := by
  have hzeroRaw : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 125000 })
    [bitMaskPath7, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState7, bitSquaredState, bitMaskedState7, bitMaskedState,
      bitLoopState, bitPC, nonzeroState, callerRest, Dispatch.wordEntryState,
      Main.headerState, initialState, UnrollPCs.copyPC7, hzeroRaw]


set_option linter.unusedSimpArgs false in
theorem run_bitProduct (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitProductPath7
      (bitMaskedState7 input outer byte offset acc base) =
        some (bitProductState7 input outer byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitProductPath7, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitMaskedState7, bitMaskedState, bitProductState7, bitProductState,
      bitLoopState, bitPC, nonzeroState, callerRest, Dispatch.wordEntryState,
      Main.headerState, initialState, UnrollPCs.copyPC7]


set_option linter.unusedSimpArgs false in
theorem run_bitChoose (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitChoosePath7
      (bitProductState7 input outer byte offset acc base) =
        some (bitSelectedState7 input outer byte offset acc base) := by
  simp (config := { maxSteps := 150000 })
    [bitChoosePath7, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitProductState7, bitProductState, bitSelectedState7, bitSelectedState,
      bitLoopState, bitPC, bitStep, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UnrollPCs.copyPC7]


set_option linter.unusedSimpArgs false in
theorem run_bitAdvance (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath7
      (bitSelectedState7 input outer byte offset acc base) =
        some (bitUnrollState input outer (7 + 1) byte offset
          (bitStep input byte 7 acc base) base) := by
  have hsucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 7) (b := 1) (by omega : 7 + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat 7 =
      UInt256.ofNat (7 + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hsucc'
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitAdvancePath7, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSelectedState7, bitSelectedState, bitUnrollState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC7, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hsucc', hincLeft, honeWord]



end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7
