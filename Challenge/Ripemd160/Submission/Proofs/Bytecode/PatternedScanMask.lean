import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjection
open EvmSemantics EvmSemantics.EVM

theorem shiftRight_xor (a b shift : UInt256) :
    UInt256.shiftRight (UInt256.xor a b) shift =
      UInt256.xor (UInt256.shiftRight a shift) (UInt256.shiftRight b shift) := by
  unfold UInt256.shiftRight
  by_cases h : shift.toNat ≥ 256
  · rw [if_pos h, if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h, if_neg h]
    unfold UInt256.xor
    congr 1
    apply Fin.ext
    change (Fin.shiftRight (Fin.xor a.val b.val) shift.val).val =
      (Fin.xor (Fin.shiftRight a.val shift.val) (Fin.shiftRight b.val shift.val)).val
    simp only [Fin.shiftRight, Fin.xor]
    change (((a.val.val ^^^ b.val.val) % UInt256.size) >>> shift.toNat) % UInt256.size =
      (((a.val.val >>> shift.toNat) % UInt256.size) ^^^
        ((b.val.val >>> shift.toNat) % UInt256.size)) % UInt256.size
    have hab : a.val.val ^^^ b.val.val < UInt256.size :=
      Nat.xor_lt_two_pow a.val.isLt b.val.isLt
    have ha : a.val.val >>> shift.toNat < UInt256.size :=
      Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.val.isLt
    have hb : b.val.val >>> shift.toNat < UInt256.size :=
      Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) b.val.isLt
    have habs : (a.val.val ^^^ b.val.val) >>> shift.toNat < UInt256.size :=
      Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hab
    have hshifts : (a.val.val >>> shift.toNat) ^^^ (b.val.val >>> shift.toNat) < UInt256.size :=
      Nat.xor_lt_two_pow ha hb
    rw [Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt habs,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hshifts]
    exact Nat.shiftRight_xor_distrib

theorem shifted_xor_zero_iff (a b shift : UInt256) :
    UInt256.shiftRight (UInt256.xor a b) shift = 0 ↔
      UInt256.shiftRight a shift = UInt256.shiftRight b shift := by
  rw [shiftRight_xor, KnownInputLogic.wordXor_eq_zero_iff]

theorem shifted_readWord_xor_zero_iff (input reference : ByteArray) (offset width : Nat)
    (hpos : 0 < width) (hwidth : width ≤ 32) :
    UInt256.shiftRight
      (UInt256.xor (MachineState.readWord input offset) (MachineState.readWord reference offset))
      (UInt256.ofNat ((32 - width) * 8)) = 0 ↔
      UInt256.ofNat (Precompile.bytesToNatPadded input offset width) =
        UInt256.ofNat (Precompile.bytesToNatPadded reference offset width) := by
  rw [shifted_xor_zero_iff,
      Challenge.EvmProof.Bytes.shiftRight_readWord input offset width hpos hwidth,
      Challenge.EvmProof.Bytes.shiftRight_readWord reference offset width hpos hwidth]

theorem bytesToNatPadded_eq_iff (input reference : ByteArray) (offset width : Nat) :
    Precompile.bytesToNatPadded input offset width =
        Precompile.bytesToNatPadded reference offset width ↔
      ∀ i, i < width → YulSemantics.EVM.byteFrom input.toList (offset + i) =
        YulSemantics.EVM.byteFrom reference.toList (offset + i) := by
  induction width with
  | zero => simp
  | succ n ih =>
    rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ,
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
    have ha := (YulSemantics.EVM.byteFrom input.toList (offset + n)).toNat_lt
    have hb := (YulSemantics.EVM.byteFrom reference.toList (offset + n)).toNat_lt
    constructor
    · intro h
      have hp : Precompile.bytesToNatPadded input offset n =
          Precompile.bytesToNatPadded reference offset n := by omega
      have ht : YulSemantics.EVM.byteFrom input.toList (offset + n) =
          YulSemantics.EVM.byteFrom reference.toList (offset + n) := by
        apply UInt8.ext
        omega
      intro i hi
      by_cases he : i = n
      · subst i
        exact ht
      · exact ih.mp hp i (by omega)
    · intro h
      rw [ih.mpr (fun i hi => h i (by omega)), h n (by omega)]

theorem shifted_readWord_xor_zero_iff_bytes (input reference : ByteArray) (offset width : Nat)
    (hpos : 0 < width) (hwidth : width ≤ 32) :
    UInt256.shiftRight
      (UInt256.xor (MachineState.readWord input offset) (MachineState.readWord reference offset))
      (UInt256.ofNat ((32 - width) * 8)) = 0 ↔
      ∀ i, i < width → YulSemantics.EVM.byteFrom input.toList (offset + i) =
        YulSemantics.EVM.byteFrom reference.toList (offset + i) := by
  rw [shifted_readWord_xor_zero_iff input reference offset width hpos hwidth]
  have hpow : 256 ^ width ≤ 2 ^ 256 := by
    calc
      256 ^ width ≤ 256 ^ 32 := Nat.pow_le_pow_right (by omega) hwidth
      _ = 2 ^ 256 := by norm_num
  have ha := (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset width).trans_le hpow
  have hb := (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow reference offset width).trans_le hpow
  constructor
  · intro h
    apply (bytesToNatPadded_eq_iff input reference offset width).mp
    have hv := congrArg UInt256.toNat h
    simpa only [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv
  · intro h
    rw [(bytesToNatPadded_eq_iff input reference offset width).mpr h]

theorem byteFrom_getElem (bytes : ByteArray) (i : Nat) (hi : i < bytes.size) :
    YulSemantics.EVM.byteFrom bytes.toList i = bytes[i] := by
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
    Array.getElem?_eq_getElem hi, Option.getD_some]
  rfl

theorem eq_of_masked_words (input reference : ByteArray) (hsize : input.size = reference.size)
    (hw : ∀ j, 32 * j < reference.size →
      UInt256.shiftRight
        (UInt256.xor (MachineState.readWord input (32 * j))
          (MachineState.readWord reference (32 * j)))
        (UInt256.ofNat ((32 - min 32 (reference.size - 32 * j)) * 8)) = 0) :
    input = reference := by
  apply ByteArray.ext_getElem hsize
  intro i hi hir
  have hstart : 32 * (i / 32) < reference.size := by omega
  have hpos : 0 < min 32 (reference.size - 32 * (i / 32)) := by omega
  have hwidth : min 32 (reference.size - 32 * (i / 32)) ≤ 32 := Nat.min_le_left _ _
  have hrem : i % 32 < min 32 (reference.size - 32 * (i / 32)) := by omega
  have hbyte := (shifted_readWord_xor_zero_iff_bytes input reference
    (32 * (i / 32)) (min 32 (reference.size - 32 * (i / 32))) hpos hwidth).mp
    (hw (i / 32) hstart) (i % 32) hrem
  have hindex : 32 * (i / 32) + i % 32 = i := by omega
  rw [hindex, byteFrom_getElem input i hi, byteFrom_getElem reference i hir] at hbyte
  exact hbyte

def guardedAcc (input : ByteArray) (expected shift : Nat → UInt256) : Nat → UInt256
  | 0 => 0
  | n + 1 => UInt256.lor
      (UInt256.shiftRight (UInt256.xor (MachineState.readWord input (32 * n)) (expected n))
        (shift n))
      (guardedAcc input expected shift n)

theorem guardedAcc_zero_iff (input : ByteArray) (expected shift : Nat → UInt256) (n : Nat) :
    guardedAcc input expected shift n = 0 ↔ ∀ j, j < n →
      UInt256.shiftRight (UInt256.xor (MachineState.readWord input (32 * j)) (expected j))
        (shift j) = 0 := by
  induction n with
  | zero => simp [guardedAcc]
  | succ n ih =>
    rw [guardedAcc, KnownInputLogic.wordOr_eq_zero_iff, ih]
    constructor
    · rintro ⟨hlast, hprev⟩ j hj
      by_cases he : j = n
      · subst j; exact hlast
      · exact hprev j (by omega)
    · intro h
      exact ⟨h n (by omega), fun j hj => h j (by omega)⟩

theorem guardedAcc_zero_iff_eq (input reference : ByteArray)
    (expected : Nat → UInt256) (n : Nat)
    (hsize : input.size = reference.size) (hcover : reference.size ≤ 32 * n)
    (hguard : ∀ j, j < n →
      UInt256.shiftRight (expected j)
          (UInt256.ofNat ((32 - min 32 (reference.size - 32 * j)) * 8)) =
        UInt256.shiftRight (MachineState.readWord reference (32 * j))
          (UInt256.ofNat ((32 - min 32 (reference.size - 32 * j)) * 8))) :
    guardedAcc input expected
      (fun j => UInt256.ofNat ((32 - min 32 (reference.size - 32 * j)) * 8)) n = 0 ↔
      input = reference := by
  rw [guardedAcc_zero_iff]
  constructor
  · intro h
    apply eq_of_masked_words input reference hsize
    intro j hj
    have hjn : j < n := by omega
    have hp := (shifted_xor_zero_iff _ _ _).mp (h j hjn)
    rw [hguard j hjn] at hp
    exact (shifted_xor_zero_iff _ _ _).mpr hp
  · rintro rfl
    intro j hj
    apply (shifted_xor_zero_iff _ _ _).mpr
    exact (hguard j hj).symm

end Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjection
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjection.shiftRight_xor
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjection.shifted_readWord_xor_zero_iff

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjection.shifted_readWord_xor_zero_iff_bytes

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjection.eq_of_masked_words

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjection.guardedAcc_zero_iff_eq

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjectionInstances
open EvmSemantics EvmSemantics.EVM
open TailProjection PatternedInputData PatternedSwar

def data376 : ByteArray := patternedInput.extract 0 376
@[simp] theorem data376_size : data376.size = 376 := by
  simp [data376, patternedInput_size]

def wordShift (length j : Nat) : UInt256 :=
  UInt256.ofNat ((32 - min 32 (length - 32 * j)) * 8)

@[simp] theorem data376_getElem (i : Nat) (hi : i < data376.size) :
    data376[i] = expectedByte i := by
  simp only [data376, ByteArray.getElem_extract, Nat.zero_add]
  apply patternedInput_getElem

theorem byteFrom_data376 (i : Nat) (hi : i < 376) :
    YulSemantics.EVM.byteFrom data376.toList i = PatternedWordData.paddedByte i := by
  have hdata : i < data376.size := by rw [data376_size]; exact hi
  rw [byteFrom_getElem data376 i hdata, data376_getElem]
  simp only [PatternedWordData.paddedByte, if_pos (show i < 1000 by omega)]

theorem bytesToNatPadded_data376 (off width : Nat) (hfit : off + width ≤ 376) :
    Precompile.bytesToNatPadded data376 off width =
      Precompile.bytesToNatPadded patternedInput off width := by
  apply (bytesToNatPadded_eq_iff data376 patternedInput off width).mpr
  intro i hi
  rw [byteFrom_data376 (off + i) (by omega), PatternedWordLogic.byteFrom_patterned]

theorem guardWord_projection_376 (j : Nat) (hj : j < 12) :
    UInt256.shiftRight (guardWord j) (wordShift 376 j) =
      UInt256.shiftRight (MachineState.readWord data376 (32 * j)) (wordShift 376 j) := by
  have hg : guardWord j = PatternedWordData.expectedWordAt j := by
    interval_cases j <;> simp
  have hp : 0 < min 32 (376 - 32 * j) := by omega
  have hw : min 32 (376 - 32 * j) ≤ 32 := Nat.min_le_left _ _
  rw [hg, ← PatternedWordLogic.readWord_patterned j, wordShift,
    Challenge.EvmProof.Bytes.shiftRight_readWord patternedInput (32 * j) _ hp hw,
    Challenge.EvmProof.Bytes.shiftRight_readWord data376 (32 * j) _ hp hw,
    bytesToNatPadded_data376 (32 * j) _ (by omega)]


def data256 : ByteArray := patternedInput.extract 0 256
@[simp] theorem data256_size : data256.size = 256 := by
  simp [data256, patternedInput_size]

@[simp] theorem data256_getElem (i : Nat) (hi : i < data256.size) :
    data256[i] = expectedByte i := by
  simp only [data256, ByteArray.getElem_extract, Nat.zero_add]
  apply patternedInput_getElem

theorem byteFrom_data256 (i : Nat) (hi : i < 256) :
    YulSemantics.EVM.byteFrom data256.toList i = PatternedWordData.paddedByte i := by
  have hdata : i < data256.size := by rw [data256_size]; exact hi
  rw [byteFrom_getElem data256 i hdata, data256_getElem]
  simp only [PatternedWordData.paddedByte, if_pos (show i < 1000 by omega)]

theorem bytesToNatPadded_data256 (off width : Nat) (hfit : off + width ≤ 256) :
    Precompile.bytesToNatPadded data256 off width =
      Precompile.bytesToNatPadded patternedInput off width := by
  apply (bytesToNatPadded_eq_iff data256 patternedInput off width).mpr
  intro i hi
  rw [byteFrom_data256 (off + i) (by omega), PatternedWordLogic.byteFrom_patterned]

theorem guardWord_projection_256 (j : Nat) (hj : j < 8) :
    UInt256.shiftRight (guardWord j) (wordShift 256 j) =
      UInt256.shiftRight (MachineState.readWord data256 (32 * j)) (wordShift 256 j) := by
  have hg : guardWord j = PatternedWordData.expectedWordAt j := by
    interval_cases j <;> simp
  have hp : 0 < min 32 (256 - 32 * j) := by omega
  have hw : min 32 (256 - 32 * j) ≤ 32 := Nat.min_le_left _ _
  rw [hg, ← PatternedWordLogic.readWord_patterned j, wordShift,
    Challenge.EvmProof.Bytes.shiftRight_readWord patternedInput (32 * j) _ hp hw,
    Challenge.EvmProof.Bytes.shiftRight_readWord data256 (32 * j) _ hp hw,
    bytesToNatPadded_data256 (32 * j) _ (by omega)]

theorem guardWord_projection_1000 (j : Nat) (hj : j < 32) :
    UInt256.shiftRight (guardWord j) (wordShift 1000 j) =
      UInt256.shiftRight (MachineState.readWord patternedInput (32 * j)) (wordShift 1000 j) := by
  rw [PatternedWordLogic.readWord_patterned]
  interval_cases j <;> simp
  decide

theorem acc376_zero_iff (input : ByteArray) (hsize : input.size = 376) :
    guardedAcc input guardWord (wordShift 376) 12 = 0 ↔ input = data376 := by
  change guardedAcc input guardWord (fun j => UInt256.ofNat ((32 - min 32 (376 - 32 * j)) * 8)) 12 = 0 ↔ input = data376
  have hs : input.size = data376.size := by simpa only [data376_size]
  have hc : data376.size ≤ 32 * 12 := by rw [data376_size]; omega
  simpa only [data376_size, wordShift] using
    guardedAcc_zero_iff_eq input data376 guardWord 12 hs hc
      (by simpa only [data376_size, wordShift] using guardWord_projection_376)

theorem acc256_zero_iff (input : ByteArray) (hsize : input.size = 256) :
    guardedAcc input guardWord (wordShift 256) 8 = 0 ↔ input = data256 := by
  change guardedAcc input guardWord (fun j => UInt256.ofNat ((32 - min 32 (256 - 32 * j)) * 8)) 8 = 0 ↔ input = data256
  have hs : input.size = data256.size := by simpa only [data256_size]
  have hc : data256.size ≤ 32 * 8 := by change 256 ≤ 32 * 8; norm_num
  simpa only [data256_size, wordShift] using
    guardedAcc_zero_iff_eq input data256 guardWord 8 hs hc
      (by simpa only [data256_size, wordShift] using guardWord_projection_256)

theorem acc1000_zero_iff (input : ByteArray) (hsize : input.size = 1000) :
    guardedAcc input guardWord (wordShift 1000) 32 = 0 ↔ input = patternedInput := by
  change guardedAcc input guardWord (fun j => UInt256.ofNat ((32 - min 32 (1000 - 32 * j)) * 8)) 32 = 0 ↔ input = patternedInput
  have hs : input.size = patternedInput.size := by simpa only [patternedInput_size]
  have hc : patternedInput.size ≤ 32 * 32 := by rw [patternedInput_size]; omega
  simpa only [patternedInput_size, wordShift] using
    guardedAcc_zero_iff_eq input patternedInput guardWord 32 hs hc
      (by simpa only [patternedInput_size, wordShift] using guardWord_projection_1000)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjectionInstances
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjectionInstances.acc376_zero_iff
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjectionInstances.acc1000_zero_iff

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjectionInstances
open EvmSemantics

def rawShift (length : Nat) (offset : UInt256) : UInt256 :=
  let remaining := UInt256.ofNat length - offset
  let missing := UInt256.ofNat 32 - remaining
  UInt256.shiftLeft (UInt256.mul (UInt256.sgt missing 0) missing) (UInt256.ofNat 3)

theorem rawShift_376 (k : Nat) (hk : k < 12) :
    rawShift 376 (UInt256.ofNat (32 * k)) = wordShift 376 k := by
  interval_cases k <;> decide

theorem rawShift_256 (k : Nat) (hk : k < 8) :
    rawShift 256 (UInt256.ofNat (32 * k)) = wordShift 256 k := by
  interval_cases k <;> decide

theorem rawShift_1000 (k : Nat) (hk : k < 32) :
    rawShift 1000 (UInt256.ofNat (32 * k)) = wordShift 1000 k := by
  interval_cases k <;> decide

theorem lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  unfold UInt256.lor
  congr 1
  apply Fin.ext
  change (a.val.val ||| b.val.val) % UInt256.size = (b.val.val ||| a.val.val) % UInt256.size
  rw [Nat.or_comm]
end Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjectionInstances
