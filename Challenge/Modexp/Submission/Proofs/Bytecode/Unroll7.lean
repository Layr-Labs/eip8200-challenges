import Challenge.Modexp.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# Copy 7 of the unrolled exponent-bit body

The copy handles exponent bit 7.  Its six straight-line segments are the same
instructions as every other copy, at instruction indices 2022 .. 2045 and bytes
3217 .. 3242; the exit push begins at byte 3243.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7

open EvmSemantics
open EvmSemantics.EVM
open Word

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod
def bitMaskedState7 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer 0 byte offset acc base with
    pc := UInt256.ofNat (bitPC 7 + 14)
    stack := [UInt256.ofNat 0 - exponentBit byte 7,
      UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)),
      UInt256.ofNat 0, byte, offset, UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1267] ++ callerRest input

def bitProductState7 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer 0 byte offset acc base with
    pc := UInt256.ofNat (bitPC 7 + 18)
    stack := [UInt256.mulMod
        (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input))) base
        (UInt256.ofNat (modulusValue input)),
      UInt256.ofNat 0 - exponentBit byte 7,
      UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)),
      UInt256.ofNat 0, byte, offset, UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1267] ++ callerRest input

def bitSelectedState7 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer 0 byte offset acc base with
    pc := UInt256.ofNat (bitPC 7 + 23)
    stack := [bitStep input byte 7 acc base,
      UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)),
      UInt256.ofNat 0, byte, offset, UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1267] ++ callerRest input

def bitDecodePath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2022 1 1, opAt 2023 (.Dup ⟨2, by decide⟩), pushAt 2024 1 0,
   opAt 2025 .SHR, opAt 2026 .AND]

def bitSquarePath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2027 (.Dup ⟨7, by decide⟩), opAt 2028 (.Dup ⟨6, by decide⟩),
   opAt 2029 (.Dup ⟨7, by decide⟩), opAt 2030 .MULMOD]

def bitMaskPath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2031 (.Swap ⟨0, by decide⟩), pushAt 2032 0 0, opAt 2033 .SUB]

def bitProductPath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2034 (.Dup ⟨8, by decide⟩), opAt 2035 (.Dup ⟨8, by decide⟩),
   opAt 2036 (.Dup ⟨3, by decide⟩), opAt 2037 .MULMOD]

def bitChoosePath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2038 (.Dup ⟨2, by decide⟩), opAt 2039 .XOR, opAt 2040 .AND,
   opAt 2041 (.Dup ⟨1, by decide⟩), opAt 2042 .XOR]

def bitAdvancePath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2043 (.Swap ⟨5, by decide⟩), opAt 2044 .POP, opAt 2045 .POP]

set_option linter.unusedSimpArgs false in
theorem run_bitDecode (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDecodePath7
      (bitUnrollState input outer 7 byte offset acc base) =
        some (bitDecodedState input outer 7 byte offset acc base) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : 7 ≤ 7)
    (by norm_num : 7 < 2 ^ 256)
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - 7) byte.val.isLt (by omega)
  have hbyte : UInt256.ofNat byte.toNat = byte := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt byte.val.isLt
  have hshiftWord : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1Word : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitDecodePath7, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitUnrollState, bitDecodedState, bitLoopState, bitPC, exponentBit,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC7, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt, hsub, hshift, hbyte, hshiftWord, h1Word]


set_option linter.unusedSimpArgs false in
theorem run_bitSquare (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitSquarePath7
      (bitDecodedState input outer 7 byte offset acc base) =
        some (bitSquaredState input outer 7 byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitSquarePath7, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitDecodedState, bitSquaredState, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC7, List.exchange]


set_option linter.unusedSimpArgs false in
theorem run_bitMask (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitMaskPath7
      (bitSquaredState input outer 7 byte offset acc base) =
        some (bitMaskedState7 input outer byte offset acc base) := by
  have hzeroRaw : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 125000 })
    [bitMaskPath7, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState, bitMaskedState7, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC7, hzeroRaw, List.exchange]


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
      bitMaskedState7, bitProductState7, bitLoopState, bitPC,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC7]


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
      bitProductState7, bitSelectedState7, bitLoopState, bitPC, bitStep,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, UnrollPCs.copyPC7]


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
      bitSelectedState7, bitUnrollState, bitLoopState, bitPC, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      UnrollPCs.copyPC7, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hsucc', hincLeft, honeWord]


end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7
