import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestB
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSchedulesA
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Data

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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Data
