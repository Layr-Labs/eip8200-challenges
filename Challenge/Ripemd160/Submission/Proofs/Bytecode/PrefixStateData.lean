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


/-! ## Second checked block (the depth-2 ladder rung) -/

/-- Byte 127 of the vector is `0x62`. -/
theorem paddedByte_127 : PatternedWordData.paddedByte 127 = 0x62 := by decide

/-- The fourth checked word forces `128 <= input.size`: byte 127 reads
`0x62` from the word but would read zero past the end. -/
theorem size_ge_128_of_words (input : ByteArray)
    (h96 : EvmSemantics.MachineState.readWord input 96 =
      PatternedWordData.expectedWordAt 3) :
    128 <= input.size := by
  by_cases hle : 128 <= input.size
  · exact hle
  · exfalso
    have hlt : input.size < 128 := by omega
    have hword : EvmSemantics.MachineState.readWord input (32 * 3) =
        PatternedWordData.expectedWordAt 3 := by
      simpa using h96
    have hbyte := byteFrom_of_word input 3 31 (by omega) hword
    have e1 : 32 * 3 + 31 = 127 := by omega
    rw [e1] at hbyte
    have hzero : YulSemantics.EVM.byteFrom input.toList 127 = 0 := by
      rw [YulEvmCompiler.ByteArray.toList_eq_data]
      unfold YulSemantics.EVM.byteFrom
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
        Array.getElem?_eq_none
          (by have hsz : input.data.size = input.size := rfl; omega)]
      rfl
    rw [hbyte, paddedByte_127] at hzero
    exact absurd hzero (by decide)

theorem readWord_second64 (input : ByteArray)
    (h64 : EvmSemantics.MachineState.readWord input 64 =
      PatternedWordData.expectedWordAt 2)
    (h96 : EvmSemantics.MachineState.readWord input 96 =
      PatternedWordData.expectedWordAt 3)
    (j : Nat) (hj : 2 ≤ j) (hj' : j < 4) :
    EvmSemantics.MachineState.readWord input (32 * j) =
      PatternedWordData.expectedWordAt j := by
  have hdiv : j = 2 ∨ j = 3 := by omega
  cases hdiv with
  | inl h =>
    rw [h]
    simpa using h64
  | inr h =>
    rw [h]
    simpa using h96

theorem byteFrom_second64 (input : ByteArray)
    (h64 : EvmSemantics.MachineState.readWord input 64 =
      PatternedWordData.expectedWordAt 2)
    (h96 : EvmSemantics.MachineState.readWord input 96 =
      PatternedWordData.expectedWordAt 3)
    (k : Nat) (hk : 64 ≤ k) (hk' : k < 128) :
    YulSemantics.EVM.byteFrom input.toList k =
      PatternedWordData.paddedByte k := by
  have hr : k % 32 < 32 := Nat.mod_lt _ (by omega)
  have hdecomp : 32 * (k / 32) + k % 32 = k := by omega
  have hlo : 2 ≤ k / 32 := by omega
  have hhi : k / 32 < 4 := by omega
  have hw := readWord_second64 input h64 h96 (k / 32) hlo hhi
  have hbyte := byteFrom_of_word input (k / 32) (k % 32) hr hw
  rwa [hdecomp] at hbyte

theorem getElem_second64 (input : ByteArray)
    (h64 : EvmSemantics.MachineState.readWord input 64 =
      PatternedWordData.expectedWordAt 2)
    (h96 : EvmSemantics.MachineState.readWord input 96 =
      PatternedWordData.expectedWordAt 3)
    (k : Nat) (hk : 64 ≤ k) (hk' : k < 128) (hleft : k < input.size)
    (hright : k < PatternedInputData.patternedInput.size) :
    input[k]'(hleft) = PatternedInputData.patternedInput[k]'(hright) := by
  have hbyte := byteFrom_second64 input h64 h96 k hk hk'
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

theorem readLE32_second64 (input : ByteArray)
    (h64 : EvmSemantics.MachineState.readWord input 64 =
      PatternedWordData.expectedWordAt 2)
    (h96 : EvmSemantics.MachineState.readWord input 96 =
      PatternedWordData.expectedWordAt 3)
    (i : Nat) (hi : i < 16) :
    EvmSemantics.Crypto.Ripemd160.readLE32 input (64 + i * 4) =
      EvmSemantics.Crypto.Ripemd160.readLE32
        PatternedInputData.patternedInput (64 + i * 4) := by
  apply HashSpecBridge.readLE32_eq_of_byte
  intro j hj
  have hk : 64 + i * 4 + j < 128 := by omega
  have hk0 : 64 ≤ 64 + i * 4 + j := by omega
  have hsize : 128 <= input.size := size_ge_128_of_words input h96
  have hleft : 64 + i * 4 + j < input.size := by omega
  have hright : 64 + i * 4 + j < PatternedInputData.patternedInput.size := by
    rw [PatternedInputData.patternedInput_size]
    omega
  have hkk := getElem_second64 input h64 h96 (64 + i * 4 + j) hk0 hk hleft hright
  rw [dif_pos hleft, dif_pos hright]
  exact congrArg UInt8.toUInt32 hkk

theorem compressBlock_second64 (input : ByteArray)
    (h64 : EvmSemantics.MachineState.readWord input 64 =
      PatternedWordData.expectedWordAt 2)
    (h96 : EvmSemantics.MachineState.readWord input 96 =
      PatternedWordData.expectedWordAt 3) :
    EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H1 input 64 =
      EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H1
        PatternedInputData.patternedInput 64 := by
  apply HashSpecBridge.compressBlock_eq_of_readLE32
  intro i hi
  exact readLE32_second64 input h64 h96 i hi

/-- Checked second block: two more word matches send arbitrary-suffix
calldata from `H1` to `H2` after padding. -/
theorem h_secondBlock (input : ByteArray)
    (h64 : EvmSemantics.MachineState.readWord input 64 =
      PatternedWordData.expectedWordAt 2)
    (h96 : EvmSemantics.MachineState.readWord input 96 =
      PatternedWordData.expectedWordAt 3) :
    EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H1
        (Padding.paddedMessage input) 64 = PatternedDigest.H2 := by
  have hsize : 128 <= input.size := size_ge_128_of_words input h96
  have hsecond := compressBlock_second64 input h64 h96
  have hpad : Padding.paddedMessage input = input ++
      (ByteArray.mk #[0x80] ++ Padding.zeroBytes input.size ++
        Padding.lengthBytes input) := by
    unfold Padding.paddedMessage
    simp only [ByteArray.append_assoc]
  have hdrop : EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H1
        (input ++ (ByteArray.mk #[0x80] ++ Padding.zeroBytes input.size ++
          Padding.lengthBytes input)) 64 =
        EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H1
          input 64 :=
    HashSpecBridge.compressBlock_append_left _ _ _ _ (by omega)
  rw [hpad, hdrop, hsecond, PatternedDigest.compress1]
  exact PatternedDigestA.step1


/-! ## Third checked block (the depth-3 ladder rung) -/

/-- Byte 191 of the vector is `0xa2`. -/
theorem paddedByte_191 : PatternedWordData.paddedByte 191 = 0xa2 := by decide

/-- The sixth checked word forces `192 <= input.size`: byte 191 reads
`0xa2` from the word but would read zero past the end. -/
theorem size_ge_192_of_words (input : ByteArray)
    (h160 : EvmSemantics.MachineState.readWord input 160 =
      PatternedWordData.expectedWordAt 5) :
    192 <= input.size := by
  by_cases hle : 192 <= input.size
  · exact hle
  · exfalso
    have hlt : input.size < 192 := by omega
    have hword : EvmSemantics.MachineState.readWord input (32 * 5) =
        PatternedWordData.expectedWordAt 5 := by
      simpa using h160
    have hbyte := byteFrom_of_word input 5 31 (by omega) hword
    have e1 : 32 * 5 + 31 = 191 := by omega
    rw [e1] at hbyte
    have hzero : YulSemantics.EVM.byteFrom input.toList 191 = 0 := by
      rw [YulEvmCompiler.ByteArray.toList_eq_data]
      unfold YulSemantics.EVM.byteFrom
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
        Array.getElem?_eq_none
          (by have hsz : input.data.size = input.size := rfl; omega)]
      rfl
    rw [hbyte, paddedByte_191] at hzero
    exact absurd hzero (by decide)

theorem readWord_third64 (input : ByteArray)
    (h128 : EvmSemantics.MachineState.readWord input 128 =
      PatternedWordData.expectedWordAt 4)
    (h160 : EvmSemantics.MachineState.readWord input 160 =
      PatternedWordData.expectedWordAt 5)
    (j : Nat) (hj : 4 ≤ j) (hj' : j < 6) :
    EvmSemantics.MachineState.readWord input (32 * j) =
      PatternedWordData.expectedWordAt j := by
  have hdiv : j = 4 ∨ j = 5 := by omega
  cases hdiv with
  | inl h =>
    rw [h]
    simpa using h128
  | inr h =>
    rw [h]
    simpa using h160

theorem byteFrom_third64 (input : ByteArray)
    (h128 : EvmSemantics.MachineState.readWord input 128 =
      PatternedWordData.expectedWordAt 4)
    (h160 : EvmSemantics.MachineState.readWord input 160 =
      PatternedWordData.expectedWordAt 5)
    (k : Nat) (hk : 128 ≤ k) (hk' : k < 192) :
    YulSemantics.EVM.byteFrom input.toList k =
      PatternedWordData.paddedByte k := by
  have hr : k % 32 < 32 := Nat.mod_lt _ (by omega)
  have hdecomp : 32 * (k / 32) + k % 32 = k := by omega
  have hlo : 4 ≤ k / 32 := by omega
  have hhi : k / 32 < 6 := by omega
  have hw := readWord_third64 input h128 h160 (k / 32) hlo hhi
  have hbyte := byteFrom_of_word input (k / 32) (k % 32) hr hw
  rwa [hdecomp] at hbyte

theorem getElem_third64 (input : ByteArray)
    (h128 : EvmSemantics.MachineState.readWord input 128 =
      PatternedWordData.expectedWordAt 4)
    (h160 : EvmSemantics.MachineState.readWord input 160 =
      PatternedWordData.expectedWordAt 5)
    (k : Nat) (hk : 128 ≤ k) (hk' : k < 192) (hleft : k < input.size)
    (hright : k < PatternedInputData.patternedInput.size) :
    input[k]'(hleft) = PatternedInputData.patternedInput[k]'(hright) := by
  have hbyte := byteFrom_third64 input h128 h160 k hk hk'
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

theorem readLE32_third64 (input : ByteArray)
    (h128 : EvmSemantics.MachineState.readWord input 128 =
      PatternedWordData.expectedWordAt 4)
    (h160 : EvmSemantics.MachineState.readWord input 160 =
      PatternedWordData.expectedWordAt 5)
    (i : Nat) (hi : i < 16) :
    EvmSemantics.Crypto.Ripemd160.readLE32 input (128 + i * 4) =
      EvmSemantics.Crypto.Ripemd160.readLE32
        PatternedInputData.patternedInput (128 + i * 4) := by
  apply HashSpecBridge.readLE32_eq_of_byte
  intro j hj
  have hk : 128 + i * 4 + j < 192 := by omega
  have hk0 : 128 ≤ 128 + i * 4 + j := by omega
  have hsize : 192 <= input.size := size_ge_192_of_words input h160
  have hleft : 128 + i * 4 + j < input.size := by omega
  have hright : 128 + i * 4 + j < PatternedInputData.patternedInput.size := by
    rw [PatternedInputData.patternedInput_size]
    omega
  have hkk := getElem_third64 input h128 h160 (128 + i * 4 + j) hk0 hk hleft hright
  rw [dif_pos hleft, dif_pos hright]
  exact congrArg UInt8.toUInt32 hkk

theorem compressBlock_third64 (input : ByteArray)
    (h128 : EvmSemantics.MachineState.readWord input 128 =
      PatternedWordData.expectedWordAt 4)
    (h160 : EvmSemantics.MachineState.readWord input 160 =
      PatternedWordData.expectedWordAt 5) :
    EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H2 input 128 =
      EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H2
        PatternedInputData.patternedInput 128 := by
  apply HashSpecBridge.compressBlock_eq_of_readLE32
  intro i hi
  exact readLE32_third64 input h128 h160 i hi

/-- Checked third block: two more word matches send arbitrary-suffix
calldata from `H2` to `H3` after padding. -/
theorem h_thirdBlock (input : ByteArray)
    (h128 : EvmSemantics.MachineState.readWord input 128 =
      PatternedWordData.expectedWordAt 4)
    (h160 : EvmSemantics.MachineState.readWord input 160 =
      PatternedWordData.expectedWordAt 5) :
    EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H2
        (Padding.paddedMessage input) 128 = PatternedDigest.H3 := by
  have hsize : 192 <= input.size := size_ge_192_of_words input h160
  have hthird := compressBlock_third64 input h128 h160
  have hpad : Padding.paddedMessage input = input ++
      (ByteArray.mk #[0x80] ++ Padding.zeroBytes input.size ++
        Padding.lengthBytes input) := by
    unfold Padding.paddedMessage
    simp only [ByteArray.append_assoc]
  have hdrop : EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H2
        (input ++ (ByteArray.mk #[0x80] ++ Padding.zeroBytes input.size ++
          Padding.lengthBytes input)) 128 =
        EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H2
          input 128 :=
    HashSpecBridge.compressBlock_append_left _ _ _ _ (by omega)
  rw [hpad, hdrop, hthird, PatternedDigest.compress2]
  exact PatternedDigestA.step2

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateData
