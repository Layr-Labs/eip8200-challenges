import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanMask
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedInputData PatternedSwar PatternedWordData TailProjection TailProjectionInstances
def data56 : ByteArray := patternedInput.extract 0 56
@[simp] theorem data56_size : data56.size = 56 := by
  simp [data56, patternedInput_size]

@[simp] theorem data56_getElem (i : Nat) (hi : i < data56.size) :
    data56[i] = expectedByte i := by
  simp only [data56, ByteArray.getElem_extract, Nat.zero_add]
  apply patternedInput_getElem

theorem byteFrom_data56 (i : Nat) (hi : i < 56) :
    YulSemantics.EVM.byteFrom data56.toList i = PatternedWordData.paddedByte i := by
  have hdata : i < data56.size := by rw [data56_size]; exact hi
  rw [byteFrom_getElem data56 i hdata, data56_getElem]
  simp only [PatternedWordData.paddedByte, if_pos (show i < 1000 by omega)]

theorem bytesToNatPadded_data56 (off width : Nat) (hfit : off + width ≤ 56) :
    Precompile.bytesToNatPadded data56 off width =
      Precompile.bytesToNatPadded patternedInput off width := by
  apply (bytesToNatPadded_eq_iff data56 patternedInput off width).mpr
  intro i hi
  rw [byteFrom_data56 (off + i) (by omega), PatternedWordLogic.byteFrom_patterned]

theorem guardWord_projection_56 (j : Nat) (hj : j < 2) :
    UInt256.shiftRight (guardWord j) (wordShift 56 j) =
      UInt256.shiftRight (MachineState.readWord data56 (32 * j)) (wordShift 56 j) := by
  have hg : guardWord j = PatternedWordData.expectedWordAt j := by
    interval_cases j <;> simp
  have hp : 0 < min 32 (56 - 32 * j) := by omega
  have hw : min 32 (56 - 32 * j) ≤ 32 := Nat.min_le_left _ _
  rw [hg, ← PatternedWordLogic.readWord_patterned j, wordShift,
    Challenge.EvmProof.Bytes.shiftRight_readWord patternedInput (32 * j) _ hp hw,
    Challenge.EvmProof.Bytes.shiftRight_readWord data56 (32 * j) _ hp hw,
    bytesToNatPadded_data56 (32 * j) _ (by omega)]

theorem rawShift_56 (k : Nat) (hk : k < 2) :
    rawShift 56 (UInt256.ofNat (32 * k)) = wordShift 56 k := by
  interval_cases k <;> decide

theorem scanAcc_eq_guardedAcc_56 (input : ByteArray) (hsize : input.size = 56)
    (n : Nat) (hn : n ≤ 2) :
    scanAcc input n = guardedAcc input guardWord (wordShift 56) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scanAcc, guardedAcc, ih (by omega)]
    rw [maskShift, hsize, rawShift_56 n (by omega)]
    exact lor_comm _ _

theorem scanAcc_zero_iff_eq_56 (input : ByteArray) (hsize : input.size = 56) :
    scanAcc input 2 = 0 ↔ input = data56 := by
  rw [scanAcc_eq_guardedAcc_56 input hsize 2 (by omega)]
  change guardedAcc input guardWord (fun j => UInt256.ofNat ((32 - min 32 (56 - 32 * j)) * 8)) 2 = 0 ↔ input = data56
  have hs : input.size = data56.size := by simpa only [data56_size] using hsize
  have hc : data56.size ≤ 32 * 2 := by rw [data56_size]; decide
  simpa only [data56_size, wordShift] using
    (guardedAcc_zero_iff_eq input data56 guardWord 2 hs hc
      (by simpa only [data56_size, wordShift] using guardWord_projection_56))
#print axioms scanAcc_zero_iff_eq_56
def data120 : ByteArray := patternedInput.extract 0 120
@[simp] theorem data120_size : data120.size = 120 := by
  simp [data120, patternedInput_size]

@[simp] theorem data120_getElem (i : Nat) (hi : i < data120.size) :
    data120[i] = expectedByte i := by
  simp only [data120, ByteArray.getElem_extract, Nat.zero_add]
  apply patternedInput_getElem

theorem byteFrom_data120 (i : Nat) (hi : i < 120) :
    YulSemantics.EVM.byteFrom data120.toList i = PatternedWordData.paddedByte i := by
  have hdata : i < data120.size := by rw [data120_size]; exact hi
  rw [byteFrom_getElem data120 i hdata, data120_getElem]
  simp only [PatternedWordData.paddedByte, if_pos (show i < 1000 by omega)]

theorem bytesToNatPadded_data120 (off width : Nat) (hfit : off + width ≤ 120) :
    Precompile.bytesToNatPadded data120 off width =
      Precompile.bytesToNatPadded patternedInput off width := by
  apply (bytesToNatPadded_eq_iff data120 patternedInput off width).mpr
  intro i hi
  rw [byteFrom_data120 (off + i) (by omega), PatternedWordLogic.byteFrom_patterned]

theorem guardWord_projection_120 (j : Nat) (hj : j < 4) :
    UInt256.shiftRight (guardWord j) (wordShift 120 j) =
      UInt256.shiftRight (MachineState.readWord data120 (32 * j)) (wordShift 120 j) := by
  have hg : guardWord j = PatternedWordData.expectedWordAt j := by
    interval_cases j <;> simp
  have hp : 0 < min 32 (120 - 32 * j) := by omega
  have hw : min 32 (120 - 32 * j) ≤ 32 := Nat.min_le_left _ _
  rw [hg, ← PatternedWordLogic.readWord_patterned j, wordShift,
    Challenge.EvmProof.Bytes.shiftRight_readWord patternedInput (32 * j) _ hp hw,
    Challenge.EvmProof.Bytes.shiftRight_readWord data120 (32 * j) _ hp hw,
    bytesToNatPadded_data120 (32 * j) _ (by omega)]

theorem rawShift_120 (k : Nat) (hk : k < 4) :
    rawShift 120 (UInt256.ofNat (32 * k)) = wordShift 120 k := by
  interval_cases k <;> decide

theorem scanAcc_eq_guardedAcc_120 (input : ByteArray) (hsize : input.size = 120)
    (n : Nat) (hn : n ≤ 4) :
    scanAcc input n = guardedAcc input guardWord (wordShift 120) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scanAcc, guardedAcc, ih (by omega)]
    rw [maskShift, hsize, rawShift_120 n (by omega)]
    exact lor_comm _ _

theorem scanAcc_zero_iff_eq_120 (input : ByteArray) (hsize : input.size = 120) :
    scanAcc input 4 = 0 ↔ input = data120 := by
  rw [scanAcc_eq_guardedAcc_120 input hsize 4 (by omega)]
  change guardedAcc input guardWord (fun j => UInt256.ofNat ((32 - min 32 (120 - 32 * j)) * 8)) 4 = 0 ↔ input = data120
  have hs : input.size = data120.size := by simpa only [data120_size] using hsize
  have hc : data120.size ≤ 32 * 4 := by rw [data120_size]; decide
  simpa only [data120_size, wordShift] using
    (guardedAcc_zero_iff_eq input data120 guardWord 4 hs hc
      (by simpa only [data120_size, wordShift] using guardWord_projection_120))
#print axioms scanAcc_zero_iff_eq_120
def data63 : ByteArray := patternedInput.extract 0 63
@[simp] theorem data63_size : data63.size = 63 := by
  simp [data63, patternedInput_size]

@[simp] theorem data63_getElem (i : Nat) (hi : i < data63.size) :
    data63[i] = expectedByte i := by
  simp only [data63, ByteArray.getElem_extract, Nat.zero_add]
  apply patternedInput_getElem

theorem byteFrom_data63 (i : Nat) (hi : i < 63) :
    YulSemantics.EVM.byteFrom data63.toList i = PatternedWordData.paddedByte i := by
  have hdata : i < data63.size := by rw [data63_size]; exact hi
  rw [byteFrom_getElem data63 i hdata, data63_getElem]
  simp only [PatternedWordData.paddedByte, if_pos (show i < 1000 by omega)]

theorem bytesToNatPadded_data63 (off width : Nat) (hfit : off + width ≤ 63) :
    Precompile.bytesToNatPadded data63 off width =
      Precompile.bytesToNatPadded patternedInput off width := by
  apply (bytesToNatPadded_eq_iff data63 patternedInput off width).mpr
  intro i hi
  rw [byteFrom_data63 (off + i) (by omega), PatternedWordLogic.byteFrom_patterned]

theorem guardWord_projection_63 (j : Nat) (hj : j < 2) :
    UInt256.shiftRight (guardWord j) (wordShift 63 j) =
      UInt256.shiftRight (MachineState.readWord data63 (32 * j)) (wordShift 63 j) := by
  have hg : guardWord j = PatternedWordData.expectedWordAt j := by
    interval_cases j <;> simp
  have hp : 0 < min 32 (63 - 32 * j) := by omega
  have hw : min 32 (63 - 32 * j) ≤ 32 := Nat.min_le_left _ _
  rw [hg, ← PatternedWordLogic.readWord_patterned j, wordShift,
    Challenge.EvmProof.Bytes.shiftRight_readWord patternedInput (32 * j) _ hp hw,
    Challenge.EvmProof.Bytes.shiftRight_readWord data63 (32 * j) _ hp hw,
    bytesToNatPadded_data63 (32 * j) _ (by omega)]

theorem rawShift_63 (k : Nat) (hk : k < 2) :
    rawShift 63 (UInt256.ofNat (32 * k)) = wordShift 63 k := by
  interval_cases k <;> decide

theorem scanAcc_eq_guardedAcc_63 (input : ByteArray) (hsize : input.size = 63)
    (n : Nat) (hn : n ≤ 2) :
    scanAcc input n = guardedAcc input guardWord (wordShift 63) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scanAcc, guardedAcc, ih (by omega)]
    rw [maskShift, hsize, rawShift_63 n (by omega)]
    exact lor_comm _ _

theorem scanAcc_zero_iff_eq_63 (input : ByteArray) (hsize : input.size = 63) :
    scanAcc input 2 = 0 ↔ input = data63 := by
  rw [scanAcc_eq_guardedAcc_63 input hsize 2 (by omega)]
  change guardedAcc input guardWord (fun j => UInt256.ofNat ((32 - min 32 (63 - 32 * j)) * 8)) 2 = 0 ↔ input = data63
  have hs : input.size = data63.size := by simpa only [data63_size] using hsize
  have hc : data63.size ≤ 32 * 2 := by rw [data63_size]; decide
  simpa only [data63_size, wordShift] using
    (guardedAcc_zero_iff_eq input data63 guardWord 2 hs hc
      (by simpa only [data63_size, wordShift] using guardWord_projection_63))
#print axioms scanAcc_zero_iff_eq_63
def data64 : ByteArray := patternedInput.extract 0 64
@[simp] theorem data64_size : data64.size = 64 := by
  simp [data64, patternedInput_size]

@[simp] theorem data64_getElem (i : Nat) (hi : i < data64.size) :
    data64[i] = expectedByte i := by
  simp only [data64, ByteArray.getElem_extract, Nat.zero_add]
  apply patternedInput_getElem

theorem byteFrom_data64 (i : Nat) (hi : i < 64) :
    YulSemantics.EVM.byteFrom data64.toList i = PatternedWordData.paddedByte i := by
  have hdata : i < data64.size := by rw [data64_size]; exact hi
  rw [byteFrom_getElem data64 i hdata, data64_getElem]
  simp only [PatternedWordData.paddedByte, if_pos (show i < 1000 by omega)]

theorem bytesToNatPadded_data64 (off width : Nat) (hfit : off + width ≤ 64) :
    Precompile.bytesToNatPadded data64 off width =
      Precompile.bytesToNatPadded patternedInput off width := by
  apply (bytesToNatPadded_eq_iff data64 patternedInput off width).mpr
  intro i hi
  rw [byteFrom_data64 (off + i) (by omega), PatternedWordLogic.byteFrom_patterned]

theorem guardWord_projection_64 (j : Nat) (hj : j < 2) :
    UInt256.shiftRight (guardWord j) (wordShift 64 j) =
      UInt256.shiftRight (MachineState.readWord data64 (32 * j)) (wordShift 64 j) := by
  have hg : guardWord j = PatternedWordData.expectedWordAt j := by
    interval_cases j <;> simp
  have hp : 0 < min 32 (64 - 32 * j) := by omega
  have hw : min 32 (64 - 32 * j) ≤ 32 := Nat.min_le_left _ _
  rw [hg, ← PatternedWordLogic.readWord_patterned j, wordShift,
    Challenge.EvmProof.Bytes.shiftRight_readWord patternedInput (32 * j) _ hp hw,
    Challenge.EvmProof.Bytes.shiftRight_readWord data64 (32 * j) _ hp hw,
    bytesToNatPadded_data64 (32 * j) _ (by omega)]

theorem rawShift_64 (k : Nat) (hk : k < 2) :
    rawShift 64 (UInt256.ofNat (32 * k)) = wordShift 64 k := by
  interval_cases k <;> decide

theorem scanAcc_eq_guardedAcc_64 (input : ByteArray) (hsize : input.size = 64)
    (n : Nat) (hn : n ≤ 2) :
    scanAcc input n = guardedAcc input guardWord (wordShift 64) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scanAcc, guardedAcc, ih (by omega)]
    rw [maskShift, hsize, rawShift_64 n (by omega)]
    exact lor_comm _ _

theorem scanAcc_zero_iff_eq_64 (input : ByteArray) (hsize : input.size = 64) :
    scanAcc input 2 = 0 ↔ input = data64 := by
  rw [scanAcc_eq_guardedAcc_64 input hsize 2 (by omega)]
  change guardedAcc input guardWord (fun j => UInt256.ofNat ((32 - min 32 (64 - 32 * j)) * 8)) 2 = 0 ↔ input = data64
  have hs : input.size = data64.size := by simpa only [data64_size] using hsize
  have hc : data64.size ≤ 32 * 2 := by rw [data64_size]
  simpa only [data64_size, wordShift] using
    (guardedAcc_zero_iff_eq input data64 guardWord 2 hs hc
      (by simpa only [data64_size, wordShift] using guardWord_projection_64))
#print axioms scanAcc_zero_iff_eq_64

def data65 : ByteArray := patternedInput.extract 0 65
@[simp] theorem data65_size : data65.size = 65 := by
  simp [data65, patternedInput_size]

@[simp] theorem data65_getElem (i : Nat) (hi : i < data65.size) :
    data65[i] = expectedByte i := by
  simp only [data65, ByteArray.getElem_extract, Nat.zero_add]
  apply patternedInput_getElem

theorem byteFrom_data65 (i : Nat) (hi : i < 65) :
    YulSemantics.EVM.byteFrom data65.toList i = PatternedWordData.paddedByte i := by
  have hdata : i < data65.size := by rw [data65_size]; exact hi
  rw [byteFrom_getElem data65 i hdata, data65_getElem]
  simp only [PatternedWordData.paddedByte, if_pos (show i < 1000 by omega)]

theorem bytesToNatPadded_data65 (off width : Nat) (hfit : off + width ≤ 65) :
    Precompile.bytesToNatPadded data65 off width =
      Precompile.bytesToNatPadded patternedInput off width := by
  apply (bytesToNatPadded_eq_iff data65 patternedInput off width).mpr
  intro i hi
  rw [byteFrom_data65 (off + i) (by omega), PatternedWordLogic.byteFrom_patterned]

theorem guardWord_projection_65 (j : Nat) (hj : j < 3) :
    UInt256.shiftRight (guardWord j) (wordShift 65 j) =
      UInt256.shiftRight (MachineState.readWord data65 (32 * j)) (wordShift 65 j) := by
  have hg : guardWord j = PatternedWordData.expectedWordAt j := by
    interval_cases j <;> simp
  have hp : 0 < min 32 (65 - 32 * j) := by omega
  have hw : min 32 (65 - 32 * j) ≤ 32 := Nat.min_le_left _ _
  rw [hg, ← PatternedWordLogic.readWord_patterned j, wordShift,
    Challenge.EvmProof.Bytes.shiftRight_readWord patternedInput (32 * j) _ hp hw,
    Challenge.EvmProof.Bytes.shiftRight_readWord data65 (32 * j) _ hp hw,
    bytesToNatPadded_data65 (32 * j) _ (by omega)]

theorem rawShift_65 (k : Nat) (hk : k < 3) :
    rawShift 65 (UInt256.ofNat (32 * k)) = wordShift 65 k := by
  interval_cases k <;> decide

theorem scanAcc_eq_guardedAcc_65 (input : ByteArray) (hsize : input.size = 65)
    (n : Nat) (hn : n ≤ 3) :
    scanAcc input n = guardedAcc input guardWord (wordShift 65) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scanAcc, guardedAcc, ih (by omega)]
    rw [maskShift, hsize, rawShift_65 n (by omega)]
    exact lor_comm _ _

theorem scanAcc_zero_iff_eq_65 (input : ByteArray) (hsize : input.size = 65) :
    scanAcc input 3 = 0 ↔ input = data65 := by
  rw [scanAcc_eq_guardedAcc_65 input hsize 3 (by omega)]
  change guardedAcc input guardWord (fun j => UInt256.ofNat ((32 - min 32 (65 - 32 * j)) * 8)) 3 = 0 ↔ input = data65
  have hs : input.size = data65.size := by simpa only [data65_size] using hsize
  have hc : data65.size ≤ 32 * 3 := by rw [data65_size]; decide
  simpa only [data65_size, wordShift] using
    (guardedAcc_zero_iff_eq input data65 guardWord 3 hs hc
      (by simpa only [data65_size, wordShift] using guardWord_projection_65))
#print axioms scanAcc_zero_iff_eq_65

def data128 : ByteArray := patternedInput.extract 0 128
@[simp] theorem data128_size : data128.size = 128 := by
  simp [data128, patternedInput_size]

@[simp] theorem data128_getElem (i : Nat) (hi : i < data128.size) :
    data128[i] = expectedByte i := by
  simp only [data128, ByteArray.getElem_extract, Nat.zero_add]
  apply patternedInput_getElem

theorem byteFrom_data128 (i : Nat) (hi : i < 128) :
    YulSemantics.EVM.byteFrom data128.toList i = PatternedWordData.paddedByte i := by
  have hdata : i < data128.size := by rw [data128_size]; exact hi
  rw [byteFrom_getElem data128 i hdata, data128_getElem]
  simp only [PatternedWordData.paddedByte, if_pos (show i < 1000 by omega)]

theorem bytesToNatPadded_data128 (off width : Nat) (hfit : off + width ≤ 128) :
    Precompile.bytesToNatPadded data128 off width =
      Precompile.bytesToNatPadded patternedInput off width := by
  apply (bytesToNatPadded_eq_iff data128 patternedInput off width).mpr
  intro i hi
  rw [byteFrom_data128 (off + i) (by omega), PatternedWordLogic.byteFrom_patterned]

theorem guardWord_projection_128 (j : Nat) (hj : j < 4) :
    UInt256.shiftRight (guardWord j) (wordShift 128 j) =
      UInt256.shiftRight (MachineState.readWord data128 (32 * j)) (wordShift 128 j) := by
  have hg : guardWord j = PatternedWordData.expectedWordAt j := by
    interval_cases j <;> simp
  have hp : 0 < min 32 (128 - 32 * j) := by omega
  have hw : min 32 (128 - 32 * j) ≤ 32 := Nat.min_le_left _ _
  rw [hg, ← PatternedWordLogic.readWord_patterned j, wordShift,
    Challenge.EvmProof.Bytes.shiftRight_readWord patternedInput (32 * j) _ hp hw,
    Challenge.EvmProof.Bytes.shiftRight_readWord data128 (32 * j) _ hp hw,
    bytesToNatPadded_data128 (32 * j) _ (by omega)]

theorem rawShift_128 (k : Nat) (hk : k < 4) :
    rawShift 128 (UInt256.ofNat (32 * k)) = wordShift 128 k := by
  interval_cases k <;> decide

theorem scanAcc_eq_guardedAcc_128 (input : ByteArray) (hsize : input.size = 128)
    (n : Nat) (hn : n ≤ 4) :
    scanAcc input n = guardedAcc input guardWord (wordShift 128) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scanAcc, guardedAcc, ih (by omega)]
    rw [maskShift, hsize, rawShift_128 n (by omega)]
    exact lor_comm _ _

theorem scanAcc_zero_iff_eq_128 (input : ByteArray) (hsize : input.size = 128) :
    scanAcc input 4 = 0 ↔ input = data128 := by
  rw [scanAcc_eq_guardedAcc_128 input hsize 4 (by omega)]
  change guardedAcc input guardWord (fun j => UInt256.ofNat ((32 - min 32 (128 - 32 * j)) * 8)) 4 = 0 ↔ input = data128
  have hs : input.size = data128.size := by simpa only [data128_size] using hsize
  have hc : data128.size ≤ 32 * 4 := by rw [data128_size]
  simpa only [data128_size, wordShift] using
    (guardedAcc_zero_iff_eq input data128 guardWord 4 hs hc
      (by simpa only [data128_size, wordShift] using guardWord_projection_128))
#print axioms scanAcc_zero_iff_eq_128

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
