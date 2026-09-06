import Challenge.Modexp.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# Copy 3 of the unrolled exponent-bit body

The copy handles exponent bit 3.  Its six straight-line segments are the same
instructions as every other copy, at instruction indices 1922 .. 1946 and bytes
3109 .. 3135.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll3

open EvmSemantics
open EvmSemantics.EVM
open Word

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

def bitDecodePath3 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1922 1 1, opAt 1923 (.Dup ⟨2, by decide⟩), pushAt 1924 1 4,
   opAt 1925 .SHR, opAt 1926 .AND]

def bitSquarePath3 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1927 (.Dup ⟨7, by decide⟩), opAt 1928 (.Dup ⟨6, by decide⟩),
   opAt 1929 (.Dup ⟨7, by decide⟩), opAt 1930 .MULMOD]

def bitMaskPath3 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1931 (.Dup ⟨1, by decide⟩), pushAt 1932 0 0, opAt 1933 .SUB]

def bitProductPath3 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1934 (.Dup ⟨9, by decide⟩), opAt 1935 (.Dup ⟨9, by decide⟩),
   opAt 1936 (.Dup ⟨3, by decide⟩), opAt 1937 .MULMOD]

def bitChoosePath3 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1938 (.Dup ⟨2, by decide⟩), opAt 1939 .XOR, opAt 1940 .AND,
   opAt 1941 (.Dup ⟨1, by decide⟩), opAt 1942 .XOR]

def bitAdvancePath3 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1943 (.Swap ⟨6, by decide⟩), opAt 1944 .POP, opAt 1945 .POP,
   opAt 1946 .POP]

set_option linter.unusedSimpArgs false in
theorem run_bitDecode (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDecodePath3
      (bitUnrollState input outer 3 byte offset acc base) =
        some (bitDecodedState input outer 3 byte offset acc base) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : 3 ≤ 7)
    (by norm_num : 7 < 2 ^ 256)
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - 3) byte.val.isLt (by omega)
  have hbyte : UInt256.ofNat byte.toNat = byte := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt byte.val.isLt
  have hshiftWord : (4 : UInt256) = UInt256.ofNat 4 := by decide
  have h1Word : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitDecodePath3, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitUnrollState, bitDecodedState, bitLoopState, bitPC, exponentBit,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC3, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt, hsub, hshift, hbyte, hshiftWord, h1Word]


set_option linter.unusedSimpArgs false in
theorem run_bitSquare (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitSquarePath3
      (bitDecodedState input outer 3 byte offset acc base) =
        some (bitSquaredState input outer 3 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitSquarePath3, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitDecodedState, bitSquaredState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC3, List.exchange]


set_option linter.unusedSimpArgs false in
theorem run_bitMask (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitMaskPath3
      (bitSquaredState input outer 3 byte offset acc base) =
        some (bitMaskedState input outer 3 byte offset acc base) := by
  have hzeroRaw : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 125000 })
    [bitMaskPath3, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState, bitMaskedState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC3, hzeroRaw]


set_option linter.unusedSimpArgs false in
theorem run_bitProduct (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitProductPath3
      (bitMaskedState input outer 3 byte offset acc base) =
        some (bitProductState input outer 3 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitProductPath3, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitMaskedState, bitProductState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC3]


set_option linter.unusedSimpArgs false in
theorem run_bitChoose (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitChoosePath3
      (bitProductState input outer 3 byte offset acc base) =
        some (bitSelectedState input outer 3 byte offset acc base) := by
  simp (config := { maxSteps := 150000 })
    [bitChoosePath3, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitProductState, bitSelectedState, bitLoopState, bitPC, bitStep,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC3]


set_option linter.unusedSimpArgs false in
theorem run_bitAdvance (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath3
      (bitSelectedState input outer 3 byte offset acc base) =
        some (bitUnrollState input outer (3 + 1) byte offset
          (bitStep input byte 3 acc base) base) := by
  have hsucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 3) (b := 1) (by omega : 3 + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat 3 =
      UInt256.ofNat (3 + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hsucc'
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitAdvancePath3, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSelectedState, bitUnrollState, bitLoopState, bitPC, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UnrollPCs.copyPC3, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hsucc', hincLeft, honeWord]


end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll3
