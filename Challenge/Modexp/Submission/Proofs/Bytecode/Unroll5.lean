import Challenge.Modexp.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# Copy 5 of the unrolled exponent-bit body

The copy handles exponent bit 5.  Its six straight-line segments are the same
instructions as every other copy, at instruction indices 1972 .. 1996 and bytes
3163 .. 3189.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll5

open EvmSemantics
open EvmSemantics.EVM
open Word

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

def bitDecodePath5 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1972 1 1, opAt 1973 (.Dup ⟨2, by decide⟩), pushAt 1974 1 2,
   opAt 1975 .SHR, opAt 1976 .AND]

def bitSquarePath5 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1977 (.Dup ⟨7, by decide⟩), opAt 1978 (.Dup ⟨6, by decide⟩),
   opAt 1979 (.Dup ⟨7, by decide⟩), opAt 1980 .MULMOD]

def bitMaskPath5 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1981 (.Dup ⟨1, by decide⟩), pushAt 1982 0 0, opAt 1983 .SUB]

def bitProductPath5 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1984 (.Dup ⟨9, by decide⟩), opAt 1985 (.Dup ⟨9, by decide⟩),
   opAt 1986 (.Dup ⟨3, by decide⟩), opAt 1987 .MULMOD]

def bitChoosePath5 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1988 (.Dup ⟨2, by decide⟩), opAt 1989 .XOR, opAt 1990 .AND,
   opAt 1991 (.Dup ⟨1, by decide⟩), opAt 1992 .XOR]

def bitAdvancePath5 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1993 (.Swap ⟨6, by decide⟩), opAt 1994 .POP, opAt 1995 .POP,
   opAt 1996 .POP]

set_option linter.unusedSimpArgs false in
theorem run_bitDecode (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDecodePath5
      (bitUnrollState input outer 5 byte offset acc base) =
        some (bitDecodedState input outer 5 byte offset acc base) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : 5 ≤ 7)
    (by norm_num : 7 < 2 ^ 256)
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - 5) byte.val.isLt (by omega)
  have hbyte : UInt256.ofNat byte.toNat = byte := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt byte.val.isLt
  have hshiftWord : (2 : UInt256) = UInt256.ofNat 2 := by decide
  have h1Word : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitDecodePath5, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitUnrollState, bitDecodedState, bitLoopState, bitPC, exponentBit,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC5, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt, hsub, hshift, hbyte, hshiftWord, h1Word]


set_option linter.unusedSimpArgs false in
theorem run_bitSquare (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitSquarePath5
      (bitDecodedState input outer 5 byte offset acc base) =
        some (bitSquaredState input outer 5 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitSquarePath5, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitDecodedState, bitSquaredState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC5, List.exchange]


set_option linter.unusedSimpArgs false in
theorem run_bitMask (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitMaskPath5
      (bitSquaredState input outer 5 byte offset acc base) =
        some (bitMaskedState input outer 5 byte offset acc base) := by
  have hzeroRaw : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 125000 })
    [bitMaskPath5, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState, bitMaskedState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC5, hzeroRaw]


set_option linter.unusedSimpArgs false in
theorem run_bitProduct (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitProductPath5
      (bitMaskedState input outer 5 byte offset acc base) =
        some (bitProductState input outer 5 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitProductPath5, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitMaskedState, bitProductState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC5]


set_option linter.unusedSimpArgs false in
theorem run_bitChoose (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitChoosePath5
      (bitProductState input outer 5 byte offset acc base) =
        some (bitSelectedState input outer 5 byte offset acc base) := by
  simp (config := { maxSteps := 150000 })
    [bitChoosePath5, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitProductState, bitSelectedState, bitLoopState, bitPC, bitStep,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC5]


set_option linter.unusedSimpArgs false in
theorem run_bitAdvance (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath5
      (bitSelectedState input outer 5 byte offset acc base) =
        some (bitUnrollState input outer (5 + 1) byte offset
          (bitStep input byte 5 acc base) base) := by
  have hsucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 5) (b := 1) (by omega : 5 + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat 5 =
      UInt256.ofNat (5 + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hsucc'
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitAdvancePath5, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSelectedState, bitUnrollState, bitLoopState, bitPC, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UnrollPCs.copyPC5, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hsucc', hincLeft, honeWord]


end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll5
