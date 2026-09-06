import Challenge.Modexp.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# Copy 6 of the unrolled exponent-bit body

The copy handles exponent bit 6.  Its six straight-line segments are the same
instructions as every other copy, at instruction indices 1997 .. 2021 and bytes
3190 .. 3216.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll6

open EvmSemantics
open EvmSemantics.EVM
open Word

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

def bitDecodePath6 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1997 1 1, opAt 1998 (.Dup ⟨2, by decide⟩), pushAt 1999 1 1,
   opAt 2000 .SHR, opAt 2001 .AND]

def bitSquarePath6 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2002 (.Dup ⟨7, by decide⟩), opAt 2003 (.Dup ⟨6, by decide⟩),
   opAt 2004 (.Dup ⟨7, by decide⟩), opAt 2005 .MULMOD]

def bitMaskPath6 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2006 (.Dup ⟨1, by decide⟩), pushAt 2007 0 0, opAt 2008 .SUB]

def bitProductPath6 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2009 (.Dup ⟨9, by decide⟩), opAt 2010 (.Dup ⟨9, by decide⟩),
   opAt 2011 (.Dup ⟨3, by decide⟩), opAt 2012 .MULMOD]

def bitChoosePath6 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2013 (.Dup ⟨2, by decide⟩), opAt 2014 .XOR, opAt 2015 .AND,
   opAt 2016 (.Dup ⟨1, by decide⟩), opAt 2017 .XOR]

def bitAdvancePath6 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2018 (.Swap ⟨6, by decide⟩), opAt 2019 .POP, opAt 2020 .POP,
   opAt 2021 .POP]

set_option linter.unusedSimpArgs false in
theorem run_bitDecode (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDecodePath6
      (bitUnrollState input outer 6 byte offset acc base) =
        some (bitDecodedState input outer 6 byte offset acc base) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : 6 ≤ 7)
    (by norm_num : 7 < 2 ^ 256)
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - 6) byte.val.isLt (by omega)
  have hbyte : UInt256.ofNat byte.toNat = byte := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt byte.val.isLt
  have hshiftWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h1Word : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitDecodePath6, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitUnrollState, bitDecodedState, bitLoopState, bitPC, exponentBit,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC6, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt, hsub, hshift, hbyte, hshiftWord, h1Word]


set_option linter.unusedSimpArgs false in
theorem run_bitSquare (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitSquarePath6
      (bitDecodedState input outer 6 byte offset acc base) =
        some (bitSquaredState input outer 6 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitSquarePath6, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitDecodedState, bitSquaredState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC6, List.exchange]


set_option linter.unusedSimpArgs false in
theorem run_bitMask (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitMaskPath6
      (bitSquaredState input outer 6 byte offset acc base) =
        some (bitMaskedState input outer 6 byte offset acc base) := by
  have hzeroRaw : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 125000 })
    [bitMaskPath6, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState, bitMaskedState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC6, hzeroRaw]


set_option linter.unusedSimpArgs false in
theorem run_bitProduct (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitProductPath6
      (bitMaskedState input outer 6 byte offset acc base) =
        some (bitProductState input outer 6 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitProductPath6, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitMaskedState, bitProductState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC6]


set_option linter.unusedSimpArgs false in
theorem run_bitChoose (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitChoosePath6
      (bitProductState input outer 6 byte offset acc base) =
        some (bitSelectedState input outer 6 byte offset acc base) := by
  simp (config := { maxSteps := 150000 })
    [bitChoosePath6, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitProductState, bitSelectedState, bitLoopState, bitPC, bitStep,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC6]


set_option linter.unusedSimpArgs false in
theorem run_bitAdvance (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath6
      (bitSelectedState input outer 6 byte offset acc base) =
        some (bitUnrollState input outer (6 + 1) byte offset
          (bitStep input byte 6 acc base) base) := by
  have hsucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 6) (b := 1) (by omega : 6 + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat 6 =
      UInt256.ofNat (6 + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hsucc'
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitAdvancePath6, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSelectedState, bitUnrollState, bitLoopState, bitPC, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UnrollPCs.copyPC6, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hsucc', hincLeft, honeWord]


end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll6
