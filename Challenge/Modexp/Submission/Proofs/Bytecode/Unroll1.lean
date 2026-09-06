import Challenge.Modexp.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# Copy 1 of the unrolled exponent-bit body

The copy handles exponent bit 1.  Its six straight-line segments are the same
instructions as every other copy, at instruction indices 1872 .. 1896 and bytes
3055 .. 3081.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll1

open EvmSemantics
open EvmSemantics.EVM
open Word

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

def bitDecodePath1 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1872 1 1, opAt 1873 (.Dup ⟨2, by decide⟩), pushAt 1874 1 6,
   opAt 1875 .SHR, opAt 1876 .AND]

def bitSquarePath1 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1877 (.Dup ⟨7, by decide⟩), opAt 1878 (.Dup ⟨6, by decide⟩),
   opAt 1879 (.Dup ⟨7, by decide⟩), opAt 1880 .MULMOD]

def bitMaskPath1 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1881 (.Dup ⟨1, by decide⟩), pushAt 1882 0 0, opAt 1883 .SUB]

def bitProductPath1 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1884 (.Dup ⟨9, by decide⟩), opAt 1885 (.Dup ⟨9, by decide⟩),
   opAt 1886 (.Dup ⟨3, by decide⟩), opAt 1887 .MULMOD]

def bitChoosePath1 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1888 (.Dup ⟨2, by decide⟩), opAt 1889 .XOR, opAt 1890 .AND,
   opAt 1891 (.Dup ⟨1, by decide⟩), opAt 1892 .XOR]

def bitAdvancePath1 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1893 (.Swap ⟨6, by decide⟩), opAt 1894 .POP, opAt 1895 .POP,
   opAt 1896 .POP]

set_option linter.unusedSimpArgs false in
theorem run_bitDecode (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDecodePath1
      (bitUnrollState input outer 1 byte offset acc base) =
        some (bitDecodedState input outer 1 byte offset acc base) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : 1 ≤ 7)
    (by norm_num : 7 < 2 ^ 256)
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - 1) byte.val.isLt (by omega)
  have hbyte : UInt256.ofNat byte.toNat = byte := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt byte.val.isLt
  have hshiftWord : (6 : UInt256) = UInt256.ofNat 6 := by decide
  have h1Word : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitDecodePath1, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitUnrollState, bitDecodedState, bitLoopState, bitPC, exponentBit,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC1, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt, hsub, hshift, hbyte, hshiftWord, h1Word]


set_option linter.unusedSimpArgs false in
theorem run_bitSquare (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitSquarePath1
      (bitDecodedState input outer 1 byte offset acc base) =
        some (bitSquaredState input outer 1 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitSquarePath1, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitDecodedState, bitSquaredState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC1, List.exchange]


set_option linter.unusedSimpArgs false in
theorem run_bitMask (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitMaskPath1
      (bitSquaredState input outer 1 byte offset acc base) =
        some (bitMaskedState input outer 1 byte offset acc base) := by
  have hzeroRaw : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 125000 })
    [bitMaskPath1, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState, bitMaskedState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC1, hzeroRaw]


set_option linter.unusedSimpArgs false in
theorem run_bitProduct (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitProductPath1
      (bitMaskedState input outer 1 byte offset acc base) =
        some (bitProductState input outer 1 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitProductPath1, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitMaskedState, bitProductState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC1]


set_option linter.unusedSimpArgs false in
theorem run_bitChoose (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitChoosePath1
      (bitProductState input outer 1 byte offset acc base) =
        some (bitSelectedState input outer 1 byte offset acc base) := by
  simp (config := { maxSteps := 150000 })
    [bitChoosePath1, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitProductState, bitSelectedState, bitLoopState, bitPC, bitStep,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC1]


set_option linter.unusedSimpArgs false in
theorem run_bitAdvance (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath1
      (bitSelectedState input outer 1 byte offset acc base) =
        some (bitUnrollState input outer (1 + 1) byte offset
          (bitStep input byte 1 acc base) base) := by
  have hsucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1) (b := 1) (by omega : 1 + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat 1 =
      UInt256.ofNat (1 + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hsucc'
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitAdvancePath1, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSelectedState, bitUnrollState, bitLoopState, bitPC, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UnrollPCs.copyPC1, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hsucc', hincLeft, honeWord]


end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll1
