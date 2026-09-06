import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# Word-level characterization of the patterned scoring vector

The guard reads the calldata thirty-two bytes at a time and accumulates
`XOR`/`OR` differences.  The accumulator vanishes exactly when every one of the
thirty-two words agrees with the vector, and — given the size check — that
holds only for the vector itself.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic

open EvmSemantics
open EvmSemantics.EVM
open PatternedInputData PatternedWordData

/-- Byte `i` of the calldata as the guard sees it, zero past the end. -/
theorem byteFrom_patterned (i : Nat) :
    YulSemantics.EVM.byteFrom patternedInput.toList i = paddedByte i := by
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  unfold YulSemantics.EVM.byteFrom paddedByte
  have hlen : patternedInput.data.size = 1000 := patternedInput_size
  by_cases hi : i < 1000
  · have hsize : i < patternedInput.size := by
      rw [patternedInput_size]; exact hi
    have hdata : i < patternedInput.data.size := by omega
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getElem?_eq_getElem hdata]
    simp only [Option.getD_some, if_pos hi]
    rw [← ByteArray.getElem_eq_getElem_data]
    exact patternedInput_getElem i hsize
  · rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getElem?_eq_none (by omega)]
    simp only [Option.getD_none, if_neg hi]

/-- The padded big-endian reading of any prefix width. -/
theorem bytesToNatPadded_eq (off width : Nat) :
    EVM.Precompile.bytesToNatPadded patternedInput off width =
      (List.range width).foldl
        (fun acc k => acc * 256 + (paddedByte (off + k)).toNat) 0 := by
  induction width with
  | zero => simp
  | succ n ih =>
      rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ, ih, byteFrom_patterned,
        List.range_succ, List.foldl_append]
      rfl

theorem patternedWordNat_lt (j : Nat) : patternedWordNat j < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow patternedInput (32 * j) 32
  rw [bytesToNatPadded_eq] at h
  have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
  rw [hpow] at h
  exact h

/-- Every word of the vector is the constant the guard compares against. -/
theorem readWord_patterned (j : Nat) :
    MachineState.readWord patternedInput (32 * j) = expectedWordAt j := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat, expectedWordAt,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (patternedWordNat_lt j), bytesToNatPadded_eq]
  rfl

/-- Byte `r` of word `j`, read straight off the vector. -/
theorem byteAt_expectedWordAt (j r : Nat) (hr : r < 32) :
    UInt256.byteAt (UInt256.ofNat r) (expectedWordAt j) =
      UInt256.ofNat (paddedByte (32 * j + r)).toNat := by
  rw [← readWord_patterned j,
    Challenge.EvmProof.Bytes.byteAt_readWord patternedInput (32 * j) r hr,
    byteFrom_patterned]

/-- The runtime accumulator, in the order the bytecode builds it. -/
def wordAcc (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | n + 1 =>
      UInt256.lor
        (UInt256.xor (MachineState.readWord input (32 * n)) (expectedWordAt n))
        (wordAcc input n)

theorem wordAcc_zero_iff (input : ByteArray) (n : Nat) :
    wordAcc input n = 0 ↔
      ∀ j, j < n → MachineState.readWord input (32 * j) = expectedWordAt j := by
  induction n with
  | zero => simp [wordAcc]
  | succ n ih =>
      rw [wordAcc, KnownInputLogic.wordOr_eq_zero_iff,
        KnownInputLogic.wordXor_eq_zero_iff, ih]
      constructor
      · rintro ⟨hlast, hprev⟩
        intro j hj
        by_cases heq : j = n
        · subst j; exact hlast
        · exact hprev j (by omega)
      · intro hall
        exact ⟨hall n (by omega), fun j hj => hall j (by omega)⟩

/-- Size and thirty-two word checks pin the calldata to the vector. -/
theorem eq_patternedInput_of_words (input : ByteArray) (hsize : input.size = 1000)
    (hw : ∀ j, j < 32 → MachineState.readWord input (32 * j) = expectedWordAt j) :
    input = patternedInput := by
  apply ByteArray.ext_getElem
  · rw [hsize, patternedInput_size]
  · intro j hj hjtarget
    have hj1000 : j < 1000 := by simpa [hsize] using hj
    have hi : j / 32 < 32 := by omega
    have hr : j % 32 < 32 := Nat.mod_lt _ (by omega)
    have hdecomp : 32 * (j / 32) + j % 32 = j := by omega
    have hb := congrArg (UInt256.byteAt (UInt256.ofNat (j % 32))) (hw (j / 32) hi)
    rw [Challenge.EvmProof.Bytes.byteAt_readWord input (32 * (j / 32)) (j % 32) hr,
      byteAt_expectedWordAt (j / 32) (j % 32) hr, hdecomp] at hb
    have hbyte : YulSemantics.EVM.byteFrom input.toList j = paddedByte j := by
      apply UInt8.ext
      have hv := congrArg UInt256.toNat hb
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans
          (YulSemantics.EVM.byteFrom input.toList j).toNat_lt (by norm_num)),
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (paddedByte j).toNat_lt (by norm_num))] at hv
      exact hv
    have hdata : j < input.data.size := hj
    rw [YulEvmCompiler.ByteArray.toList_eq_data] at hbyte
    unfold YulSemantics.EVM.byteFrom at hbyte
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getElem?_eq_getElem hdata] at hbyte
    simp only [Option.getD_some, paddedByte, if_pos hj1000] at hbyte
    rw [patternedInput_getElem j hjtarget]
    exact hbyte

theorem wordAcc_zero_iff_eq (input : ByteArray) (hsize : input.size = 1000) :
    wordAcc input 32 = 0 ↔ input = patternedInput := by
  rw [wordAcc_zero_iff]
  constructor
  · intro hw
    exact eq_patternedInput_of_words input hsize hw
  · rintro rfl
    intro j _
    exact readWord_patterned j

theorem wordAcc_patterned : wordAcc patternedInput 32 = 0 :=
  (wordAcc_zero_iff_eq patternedInput patternedInput_size).2 rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic
