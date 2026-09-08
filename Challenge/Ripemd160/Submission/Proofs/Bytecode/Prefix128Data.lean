import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Data

open EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedWordData

def data : ByteArray := patternedInput.extract 0 128

@[simp] theorem data_size : data.size = 128 := by
  simp [data, patternedInput_size]

@[simp] theorem data_getElem (i : Nat) (hi : i < data.size) :
    data[i] = expectedByte i := by
  simp only [data, ByteArray.getElem_extract, Nat.zero_add]
  apply patternedInput_getElem

theorem byteFrom_data (i : Nat) (hi : i < 128) :
    YulSemantics.EVM.byteFrom data.toList i = paddedByte i := by
  have hdata : i < data.data.size := by change i < data.size; rw [data_size]; exact hi
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
    Array.getElem?_eq_getElem hdata]
  simp only [Option.getD_some]
  rw [← ByteArray.getElem_eq_getElem_data, data_getElem]
  simp only [paddedByte, if_pos (show i < 1000 by omega)]

private theorem bytesToNatPadded_eq (off width : Nat) (hfit : off + width ≤ 128) :
    EVM.Precompile.bytesToNatPadded data off width =
      EVM.Precompile.bytesToNatPadded patternedInput off width := by
  induction width with
  | zero => simp
  | succ n ih =>
      rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ,
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ,
        ih (by omega), byteFrom_data (off + n) (by omega),
        PatternedWordLogic.byteFrom_patterned]

theorem readWord_data (j : Nat) (hj : j < 4) :
    MachineState.readWord data (32 * j) = expectedWordAt j := by
  rw [← PatternedWordLogic.readWord_patterned j]
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat,
    Challenge.EvmProof.Bytes.readWord_toNat,
    bytesToNatPadded_eq (32 * j) 32 (by omega)]

theorem eq_data_of_words (input : ByteArray) (hsize : input.size = 128)
    (hw : ∀ j, j < 4 → MachineState.readWord input (32 * j) = expectedWordAt j) :
    input = data := by
  apply ByteArray.ext_getElem
  · rw [hsize, data_size]
  · intro j hj hjtarget
    have hj128 : j < 128 := by simpa [hsize] using hj
    have hi : j / 32 < 4 := by omega
    have hr : j % 32 < 32 := Nat.mod_lt _ (by omega)
    have hdecomp : 32 * (j / 32) + j % 32 = j := by omega
    have hb := congrArg (UInt256.byteAt (UInt256.ofNat (j % 32))) (hw (j / 32) hi)
    rw [Challenge.EvmProof.Bytes.byteAt_readWord input (32 * (j / 32)) (j % 32) hr,
      PatternedWordLogic.byteAt_expectedWordAt (j / 32) (j % 32) hr, hdecomp] at hb
    have hbyte : YulSemantics.EVM.byteFrom input.toList j = paddedByte j := by
      apply UInt8.ext
      have hv := congrArg UInt256.toNat hb
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans
          (YulSemantics.EVM.byteFrom input.toList j).toNat_lt (by norm_num)),
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (paddedByte j).toNat_lt (by norm_num))] at hv
      exact hv
    have hinput : j < input.data.size := hj
    rw [YulEvmCompiler.ByteArray.toList_eq_data] at hbyte
    unfold YulSemantics.EVM.byteFrom at hbyte
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getElem?_eq_getElem hinput] at hbyte
    simp only [Option.getD_some, paddedByte,
      if_pos (show j < 1000 by omega)] at hbyte
    rw [data_getElem j hjtarget]
    exact hbyte

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Data
