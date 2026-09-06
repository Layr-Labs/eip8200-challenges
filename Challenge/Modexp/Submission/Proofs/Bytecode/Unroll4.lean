import Challenge.Modexp.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# Copy 4 of the unrolled exponent-bit body

The copy handles exponent bit 4.  Its six straight-line segments are the same
instructions as every other copy, at instruction indices 1947 .. 1971 and bytes
3136 .. 3162.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll4

open EvmSemantics
open EvmSemantics.EVM
open Word

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

def bitDecodePath4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1947 1 1, opAt 1948 (.Dup ⟨2, by decide⟩), pushAt 1949 1 3,
   opAt 1950 .SHR, opAt 1951 .AND]

def bitSquarePath4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1952 (.Dup ⟨7, by decide⟩), opAt 1953 (.Dup ⟨6, by decide⟩),
   opAt 1954 (.Dup ⟨7, by decide⟩), opAt 1955 .MULMOD]

def bitMaskPath4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1956 (.Dup ⟨1, by decide⟩), pushAt 1957 0 0, opAt 1958 .SUB]

def bitProductPath4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1959 (.Dup ⟨9, by decide⟩), opAt 1960 (.Dup ⟨9, by decide⟩),
   opAt 1961 (.Dup ⟨3, by decide⟩), opAt 1962 .MULMOD]

def bitChoosePath4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1963 (.Dup ⟨2, by decide⟩), opAt 1964 .XOR, opAt 1965 .AND,
   opAt 1966 (.Dup ⟨1, by decide⟩), opAt 1967 .XOR]

def bitAdvancePath4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1968 (.Swap ⟨6, by decide⟩), opAt 1969 .POP, opAt 1970 .POP,
   opAt 1971 .POP]

set_option linter.unusedSimpArgs false in
theorem run_bitDecode (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDecodePath4
      (bitUnrollState input outer 4 byte offset acc base) =
        some (bitDecodedState input outer 4 byte offset acc base) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : 4 ≤ 7)
    (by norm_num : 7 < 2 ^ 256)
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - 4) byte.val.isLt (by omega)
  have hbyte : UInt256.ofNat byte.toNat = byte := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt byte.val.isLt
  have hshiftWord : (3 : UInt256) = UInt256.ofNat 3 := by decide
  have h1Word : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitDecodePath4, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitUnrollState, bitDecodedState, bitLoopState, bitPC, exponentBit,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC4, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt, hsub, hshift, hbyte, hshiftWord, h1Word]


set_option linter.unusedSimpArgs false in
theorem run_bitSquare (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitSquarePath4
      (bitDecodedState input outer 4 byte offset acc base) =
        some (bitSquaredState input outer 4 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitSquarePath4, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitDecodedState, bitSquaredState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC4, List.exchange]


set_option linter.unusedSimpArgs false in
theorem run_bitMask (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitMaskPath4
      (bitSquaredState input outer 4 byte offset acc base) =
        some (bitMaskedState input outer 4 byte offset acc base) := by
  have hzeroRaw : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 125000 })
    [bitMaskPath4, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState, bitMaskedState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC4, hzeroRaw]


set_option linter.unusedSimpArgs false in
theorem run_bitProduct (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitProductPath4
      (bitMaskedState input outer 4 byte offset acc base) =
        some (bitProductState input outer 4 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitProductPath4, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitMaskedState, bitProductState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC4]


set_option linter.unusedSimpArgs false in
theorem run_bitChoose (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitChoosePath4
      (bitProductState input outer 4 byte offset acc base) =
        some (bitSelectedState input outer 4 byte offset acc base) := by
  simp (config := { maxSteps := 150000 })
    [bitChoosePath4, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitProductState, bitSelectedState, bitLoopState, bitPC, bitStep,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC4]


set_option linter.unusedSimpArgs false in
theorem run_bitAdvance (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath4
      (bitSelectedState input outer 4 byte offset acc base) =
        some (bitUnrollState input outer (4 + 1) byte offset
          (bitStep input byte 4 acc base) base) := by
  have hsucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 4) (b := 1) (by omega : 4 + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat 4 =
      UInt256.ofNat (4 + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hsucc'
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitAdvancePath4, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSelectedState, bitUnrollState, bitLoopState, bitPC, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UnrollPCs.copyPC4, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hsucc', hincLeft, honeWord]


end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll4
