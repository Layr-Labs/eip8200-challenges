import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestA
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# Checked first-block prefix state (H8 mathematical half)

Two `CALLDATALOAD` word checks pin the first 64 calldata bytes to the
patterned vector while the suffix stays arbitrary.  Length is derived,
not assumed: byte 63 is `0x22`, nonzero past the end.  First-block
compression then equals `H1` through the `readLE32`/`compressBlock`
bridge and the closed `compress0`/`step0` certificates.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateData

/-- Byte 63 of the vector is `0x22`. -/
theorem paddedByte_63 : PatternedWordData.paddedByte 63 = 0x22 := by decide

/-- One word-indexed byte of calldata equals the vector byte. -/
theorem byteFrom_of_word (input : ByteArray) (j r : Nat) (hr : r < 32)
    (hw : EvmSemantics.MachineState.readWord input (32 * j) =
      PatternedWordData.expectedWordAt j) :
    YulSemantics.EVM.byteFrom input.toList (32 * j + r) =
      PatternedWordData.paddedByte (32 * j + r) := by
  have hb := congrArg
    (EvmSemantics.UInt256.byteAt (EvmSemantics.UInt256.ofNat r)) hw
  rw [Challenge.EvmProof.Bytes.byteAt_readWord input (32 * j) r hr,
    PatternedWordLogic.byteAt_expectedWordAt j r hr] at hb
  apply UInt8.ext
  have hv := congrArg EvmSemantics.UInt256.toNat hb
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans
      (YulSemantics.EVM.byteFrom input.toList (32 * j + r)).toNat_lt
      (by norm_num)),
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans
      (PatternedWordData.paddedByte (32 * j + r)).toNat_lt
      (by norm_num))] at hv
  exact hv

/-- The second checked word forces `64 <= input.size`: byte 63 reads
`0x22` from the word but would read zero past the end. -/
theorem size_ge_64_of_words (input : ByteArray)
    (h32 : EvmSemantics.MachineState.readWord input 32 =
      PatternedWordData.expectedWordAt 1) :
    64 <= input.size := by
  by_cases hle : 64 <= input.size
  · exact hle
  · exfalso
    have hlt : input.size < 64 := by omega
    have hword : EvmSemantics.MachineState.readWord input (32 * 1) =
        PatternedWordData.expectedWordAt 1 := by
      simpa using h32
    have hbyte := byteFrom_of_word input 1 31 (by omega) hword
    have e1 : 32 * 1 + 31 = 63 := by omega
    rw [e1] at hbyte
    have hzero : YulSemantics.EVM.byteFrom input.toList 63 = 0 := by
      rw [YulEvmCompiler.ByteArray.toList_eq_data]
      unfold YulSemantics.EVM.byteFrom
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
        Array.getElem?_eq_none
          (by have hsz : input.data.size = input.size := rfl; omega)]
      rfl
    rw [hbyte, paddedByte_63] at hzero
    exact absurd hzero (by decide)

/-- Each checked word covers its 32-byte window. -/
theorem readWord_first64 (input : ByteArray)
    (h0 : EvmSemantics.MachineState.readWord input 0 =
      PatternedWordData.expectedWordAt 0)
    (h32 : EvmSemantics.MachineState.readWord input 32 =
      PatternedWordData.expectedWordAt 1)
    (j : Nat) (hj : j < 2) :
    EvmSemantics.MachineState.readWord input (32 * j) =
      PatternedWordData.expectedWordAt j := by
  have hdiv : j = 0 ∨ j = 1 := by omega
  cases hdiv with
  | inl h =>
    rw [h]
    simpa using h0
  | inr h =>
    rw [h]
    simpa using h32

/-- Every one of the first 64 calldata bytes equals the vector byte. -/
theorem byteFrom_first64 (input : ByteArray)
    (h0 : EvmSemantics.MachineState.readWord input 0 =
      PatternedWordData.expectedWordAt 0)
    (h32 : EvmSemantics.MachineState.readWord input 32 =
      PatternedWordData.expectedWordAt 1)
    (k : Nat) (hk : k < 64) :
    YulSemantics.EVM.byteFrom input.toList k =
      PatternedWordData.paddedByte k := by
  have hr : k % 32 < 32 := Nat.mod_lt _ (by omega)
  have hdecomp : 32 * (k / 32) + k % 32 = k := by omega
  have hdiv : k / 32 < 2 := by omega
  have hw := readWord_first64 input h0 h32 (k / 32) hdiv
  have hbyte := byteFrom_of_word input (k / 32) (k % 32) hr hw
  rwa [hdecomp] at hbyte

/-- GetElem form of the first-64 equality, for direct integration use. -/
theorem getElem_first64 (input : ByteArray)
    (h0 : EvmSemantics.MachineState.readWord input 0 =
      PatternedWordData.expectedWordAt 0)
    (h32 : EvmSemantics.MachineState.readWord input 32 =
      PatternedWordData.expectedWordAt 1)
    (k : Nat) (hk : k < 64) (hleft : k < input.size)
    (hright : k < PatternedInputData.patternedInput.size) :
    input[k]'(hleft) = PatternedInputData.patternedInput[k]'(hright) := by
  have hbyte := byteFrom_first64 input h0 h32 k hk
  have hpat := PatternedWordLogic.byteFrom_patterned k
  have heq : YulSemantics.EVM.byteFrom input.toList k =
      YulSemantics.EVM.byteFrom
        PatternedInputData.patternedInput.toList k := by
    rw [hbyte, hpat]
  have hgi : YulSemantics.EVM.byteFrom input.toList k =
      input[k]'(hleft) := by
    have hdata : k < input.data.size := hleft
    rw [YulEvmCompiler.ByteArray.toList_eq_data]
    unfold YulSemantics.EVM.byteFrom
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getElem?_eq_getElem hdata, Option.getD_some]
    rfl
  have hgp : YulSemantics.EVM.byteFrom
        PatternedInputData.patternedInput.toList k =
        PatternedInputData.patternedInput[k]'(hright) := by
    have hdata : k < PatternedInputData.patternedInput.data.size := hright
    rw [YulEvmCompiler.ByteArray.toList_eq_data]
    unfold YulSemantics.EVM.byteFrom
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getElem?_eq_getElem hdata, Option.getD_some]
    rfl
  rw [← hgi, ← hgp]
  exact heq

/-- All sixteen little-endian words of the first block agree. -/
theorem readLE32_first64 (input : ByteArray)
    (h0 : EvmSemantics.MachineState.readWord input 0 =
      PatternedWordData.expectedWordAt 0)
    (h32 : EvmSemantics.MachineState.readWord input 32 =
      PatternedWordData.expectedWordAt 1)
    (i : Nat) (hi : i < 16) :
    EvmSemantics.Crypto.Ripemd160.readLE32 input (i * 4) =
      EvmSemantics.Crypto.Ripemd160.readLE32
        PatternedInputData.patternedInput (i * 4) := by
  apply HashSpecBridge.readLE32_eq_of_byte
  intro j hj
  have hk : i * 4 + j < 64 := by omega
  have hsize : 64 <= input.size := size_ge_64_of_words input h32
  have hleft : i * 4 + j < input.size := by omega
  have hright : i * 4 + j < PatternedInputData.patternedInput.size := by
    rw [PatternedInputData.patternedInput_size]
    omega
  have hkk := getElem_first64 input h0 h32 (i * 4 + j) hk hleft hright
  rw [dif_pos hleft, dif_pos hright]
  exact congrArg UInt8.toUInt32 hkk

/-- First-block compression from arbitrary-suffix calldata equals the
patterned first-block compression. -/
theorem compressBlock_first64 (input : ByteArray)
    (h0 : EvmSemantics.MachineState.readWord input 0 =
      PatternedWordData.expectedWordAt 0)
    (h32 : EvmSemantics.MachineState.readWord input 32 =
      PatternedWordData.expectedWordAt 1) :
    EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H0 input 0 =
      EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H0
        PatternedInputData.patternedInput 0 := by
  apply HashSpecBridge.compressBlock_eq_of_readLE32
  intro i hi
  have h := readLE32_first64 input h0 h32 i hi
  simpa using h

/-- Checked first block: two word matches send arbitrary-suffix calldata
to `H1` after padding. -/
theorem h8_firstBlock (input : ByteArray)
    (h0 : EvmSemantics.MachineState.readWord input 0 =
      PatternedWordData.expectedWordAt 0)
    (h32 : EvmSemantics.MachineState.readWord input 32 =
      PatternedWordData.expectedWordAt 1) :
    EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H0
        (Padding.paddedMessage input) 0 = PatternedDigest.H1 := by
  have hsize : 64 <= input.size := size_ge_64_of_words input h32
  have hfirst := compressBlock_first64 input h0 h32
  have hpad : Padding.paddedMessage input = input ++
      (ByteArray.mk #[0x80] ++ Padding.zeroBytes input.size ++
        Padding.lengthBytes input) := by
    unfold Padding.paddedMessage
    simp only [ByteArray.append_assoc]
  have hdrop : EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H0
        (input ++ (ByteArray.mk #[0x80] ++ Padding.zeroBytes input.size ++
          Padding.lengthBytes input)) 0 =
        EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H0
          input 0 :=
    HashSpecBridge.compressBlock_append_left _ _ _ _ (by omega)
  rw [hpad, hdrop, hfirst, PatternedDigest.compress0]
  exact PatternedDigestA.step0

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateData
