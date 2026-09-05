import Challenge.Modexp.Submission.Proofs.Bytecode.BigLoad
import Challenge.Modexp.Submission.Proofs.Limbs
import Mathlib.Data.Nat.Bitwise
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Functional correctness of big-endian operand loading

The execution model in `BigLoad` is deliberately instruction-shaped.  This
module connects its word arithmetic and memory writes to the mathematical
little-endian limb representation consumed by the big MODEXP path.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigLoadCorrect

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

theorem loadReverseWord_ofNat (length i : Nat) (hlength : length < 2 ^ 256)
    (hi : i < length) :
    BigLoad.loadReverseWord (UInt256.ofNat length) i =
      UInt256.ofNat (BigLoad.loadReverse length i) := by
  unfold BigLoad.loadReverseWord BigLoad.loadReverse
  rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) hlength]
  rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]

theorem loadLimbWord_ofNat (length i : Nat) (hlength : length < 2 ^ 256)
    (hi : i < length) :
    BigLoad.loadLimbWord (UInt256.ofNat length) i =
      UInt256.ofNat (BigLoad.loadLimb length i) := by
  unfold BigLoad.loadLimbWord BigLoad.loadLimb
  rw [loadReverseWord_ofNat length i hlength hi]
  have hreverse : BigLoad.loadReverse length i < 2 ^ 256 := by
    unfold BigLoad.loadReverse
    omega
  rw [Challenge.EvmProof.Word.shiftRight_ofNat hreverse (by omega)]
  congr 1
  rw [Nat.shiftRight_eq_div_pow]

theorem loadShiftWord_ofNat (length i : Nat) (hlength : length < 2 ^ 256)
    (hi : i < length) :
    BigLoad.loadShiftWord (UInt256.ofNat length) i =
      UInt256.ofNat (BigLoad.loadShift length i) := by
  unfold BigLoad.loadShiftWord BigLoad.loadShift
  rw [loadReverseWord_ofNat length i hlength hi]
  have hand : UInt256.land
      (UInt256.ofNat (BigLoad.loadReverse length i)) (UInt256.ofNat 31) =
      UInt256.ofNat (BigLoad.loadReverse length i % 32) := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_land,
      Challenge.EvmProof.Word.word_toNat_ofNat]
    have hreverse : BigLoad.loadReverse length i < 2 ^ 256 := by
      unfold BigLoad.loadReverse
      omega
    rw [Nat.mod_eq_of_lt hreverse]
    norm_num
    have hmod : BigLoad.loadReverse length i % 32 < 2 ^ 256 :=
      (Nat.mod_lt _ (by omega)).trans (by norm_num)
    change BigLoad.loadReverse length i &&& 31 =
      BigLoad.loadReverse length i % 32 % 2 ^ 256
    rw [Nat.mod_eq_of_lt hmod]
    exact Nat.and_two_pow_sub_one_eq_mod (BigLoad.loadReverse length i) 5
  rw [hand]
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by
    have hmod : BigLoad.loadReverse length i % 32 < 32 := Nat.mod_lt _ (by omega)
    norm_num
    omega)]
  congr 1
  rw [show 2 ^ 3 = 8 by norm_num]
  omega

theorem loadAt_ofNat (dst length i : Nat)
    (hlength : length < 2 ^ 256) (hi : i < length)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256) :
    (BigLoad.loadAt (UInt256.ofNat dst) length i).toNat =
      dst + 32 * BigLoad.loadLimb length i := by
  unfold BigLoad.loadAt
  rw [loadLimbWord_ofNat length i hlength hi]
  have hlimb : BigLoad.loadLimb length i < Limbs.limbCount length := by
    unfold BigLoad.loadLimb BigLoad.loadReverse Limbs.limbCount
    omega
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by
    norm_num
    omega)]
  rw [show 2 ^ 5 = 32 by norm_num]
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : dst < 2 ^ 256),
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : BigLoad.loadLimb length i * 32 < 2 ^ 256)]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem lor_eq_add_of_land_eq_zero {a b : Nat}
    (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hand : a &&& b = 0) :
    a ||| b = a + b := by
  let x : BitVec 256 := BitVec.ofFin ⟨a, ha⟩
  let y : BitVec 256 := BitVec.ofFin ⟨b, hb⟩
  have hx : x.toNat = a := by simp [x]
  have hy : y.toNat = b := by simp [y]
  have hxy : x &&& y = 0#256 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hx, hy, hand]
    rfl
  calc
    a ||| b = (x ||| y).toNat := by rw [BitVec.toNat_or, hx, hy]
    _ = (x + y).toNat := by rw [BitVec.add_eq_or_of_and_eq_zero x y hxy]
    _ = a + b := by simpa [hx, hy] using BitVec.toNat_add_of_and_eq_zero hxy

private theorem land_separated_blocks (high low shift : Nat) (hlow : low < 256) :
    (high * 2 ^ (shift + 8)) &&& (low * 2 ^ shift) = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro bit
  rw [Nat.testBit_land, Nat.testBit_mul_two_pow,
    Nat.testBit_mul_two_pow]
  by_cases hhigh : shift + 8 ≤ bit
  · have hindex : 8 ≤ bit - shift := by omega
    have hlow' : low < 2 ^ 8 := by norm_num; exact hlow
    have hpow : low < 2 ^ (bit - shift) := by
      exact hlow'.trans_le (Nat.pow_le_pow_right (by omega) hindex)
    rw [Nat.testBit_eq_false_of_lt hpow]
    simp
  · simp [hhigh]

private theorem ofDigits_set_add (radix : Nat) (digits : List Nat)
    (index delta : Nat) (hindex : index < digits.length) :
    Nat.ofDigits radix (digits.set index (digits[index] + delta)) =
      Nat.ofDigits radix digits + delta * radix ^ index := by
  induction digits generalizing index with
  | nil => simp at hindex
  | cons head tail ih =>
      cases index with
      | zero =>
          change Nat.ofDigits radix ((head + delta) :: tail) = _
          simp only [Nat.ofDigits_cons, Nat.pow_zero, Nat.mul_one]
          omega
      | succ index =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hindex
          simp only [List.set_cons_succ, List.getElem_cons_succ,
            Nat.ofDigits_cons]
          rw [ih index hindex, Nat.pow_succ]
          ring

private theorem getElem_eq_div_mod_ofDigits (radix : Nat) (digits : List Nat)
    (index : Nat) (hradix : 0 < radix) (hindex : index < digits.length)
    (hdigits : ∀ digit ∈ digits, digit < radix) :
    digits[index] = Nat.ofDigits radix digits / radix ^ index % radix := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop index hradix digits hdigits]
  rw [List.drop_eq_getElem_cons hindex]
  simp only [Nat.ofDigits_cons]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hdigits digits[index]
    (List.getElem_mem hindex))]

theorem memoryLimbs_write_at (memory : ByteArray) (ptr count index : Nat)
    (value : UInt256) (_hindex : index < count) :
    Limbs.memoryLimbs
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value.toNat 32) (ptr + 32 * index))
        ptr count =
      (Limbs.memoryLimbs memory ptr count).set index value.toNat := by
  apply List.ext_get
  · simp [Limbs.memoryLimbs]
  · intro j hjLeft hjRight
    have hj : j < count := by simpa [Limbs.memoryLimbs] using hjLeft
    rw [List.get_eq_getElem, List.get_eq_getElem]
    rw [List.getElem_set hjRight]
    split
    · next heq =>
      subst j
      simp only [Limbs.memoryLimbs, List.getElem_map, List.getElem_range]
      rw [Challenge.EvmProof.Memory.readWord_writeWord]
    · next hne =>
      simp only [Limbs.memoryLimbs, List.getElem_map, List.getElem_range]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      rcases Nat.lt_or_gt_of_ne (Ne.symm hne) with hbefore | hafter
      · left
        omega
      · right
        simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        omega

theorem value_memoryLimbs_write_add (memory : ByteArray)
    (ptr count index delta : Nat) (hindex : index < count)
    (hfit : (MachineState.readWord memory (ptr + 32 * index)).toNat + delta <
      2 ^ 256) :
    Nat.ofDigits Limbs.radix
        (Limbs.memoryLimbs
          (MachineState.writeBytes memory
            (Data.Bytes.natToBytesPadded
              ((MachineState.readWord memory (ptr + 32 * index)).toNat + delta)
              32)
            (ptr + 32 * index)) ptr count) =
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory ptr count) +
        delta * Limbs.radix ^ index := by
  let value := UInt256.ofNat
    ((MachineState.readWord memory (ptr + 32 * index)).toNat + delta)
  have hvalue : value.toNat =
      (MachineState.readWord memory (ptr + 32 * index)).toNat + delta := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  rw [← hvalue]
  change Nat.ofDigits Limbs.radix
      (Limbs.memoryLimbs
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value.toNat 32) (ptr + 32 * index))
        ptr count) = _
  rw [memoryLimbs_write_at memory ptr count index value hindex, hvalue]
  have hidxlen : index < (Limbs.memoryLimbs memory ptr count).length := by
    simpa using hindex
  have hget : (Limbs.memoryLimbs memory ptr count)[index]'hidxlen =
      (MachineState.readWord memory (ptr + 32 * index)).toNat := by
    simp [Limbs.memoryLimbs]
  rw [← hget]
  exact ofDigits_set_add Limbs.radix (Limbs.memoryLimbs memory ptr count)
    index delta (by simpa using hindex)

def partialValue (calldata : ByteArray) (offset length i : Nat) : Nat :=
  Precompile.bytesToNatPadded calldata offset i * 256 ^ (length - i)

private theorem partial_digit (headValue index rem : Nat) (hrem : rem < 32) :
    (headValue * 256 ^ (32 * index + (rem + 1)) /
          Limbs.radix ^ index) % Limbs.radix =
      (headValue % 256 ^ (31 - rem)) * 256 ^ (rem + 1) := by
  have hsplit : 31 - rem + (rem + 1) = 32 := by omega
  rw [Limbs.radix_eq]
  rw [← Nat.pow_mul, Nat.pow_add]
  have hpow : 0 < 256 ^ (32 * index) := Nat.pow_pos (by omega)
  rw [show headValue * (256 ^ (32 * index) * 256 ^ (rem + 1)) =
      256 ^ (32 * index) * (headValue * 256 ^ (rem + 1)) by ring]
  rw [Nat.mul_div_cancel_left _ hpow]
  rw [← hsplit]
  rw [Nat.pow_add 256 (31 - rem) (rem + 1)]
  exact Nat.mul_mod_mul_right (256 ^ (rem + 1)) headValue
    (256 ^ (31 - rem))

private theorem loaded_digit_factor (calldata : ByteArray)
    (offset length i : Nat) (_hlength : length < 2 ^ 256) (hi : i < length) :
    partialValue calldata offset length i /
          Limbs.radix ^ BigLoad.loadLimb length i % Limbs.radix =
      (Precompile.bytesToNatPadded calldata offset i %
          256 ^ (31 - BigLoad.loadReverse length i % 32)) *
        256 ^ (BigLoad.loadReverse length i % 32 + 1) := by
  have hrem : BigLoad.loadReverse length i % 32 < 32 :=
    Nat.mod_lt _ (by omega)
  have hrecompose :
      32 * BigLoad.loadLimb length i +
          (BigLoad.loadReverse length i % 32 + 1) = length - i := by
    unfold BigLoad.loadLimb BigLoad.loadReverse
    have hdiv := Nat.div_add_mod (length - 1 - i) 32
    omega
  unfold partialValue
  rw [← hrecompose]
  exact partial_digit _ _ _ hrem

theorem loadByte_toNat (calldata : ByteArray) (offset i : Nat) :
    (BigLoad.loadByte calldata offset i).toNat =
      (YulSemantics.EVM.byteFrom calldata.toList (offset + i)).toNat := by
  unfold BigLoad.loadByte
  rw [Challenge.EvmProof.Bytes.byteAt_zero_readWord]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact (YulSemantics.EVM.byteFrom calldata.toList
    (offset + i)).toNat_lt.trans (by norm_num)

theorem shiftedLoadByte_toNat (calldata : ByteArray) (offset length i : Nat)
    (hlength : length < 2 ^ 256) (hi : i < length) :
    (UInt256.shiftLeft (BigLoad.loadByte calldata offset i)
      (BigLoad.loadShiftWord (UInt256.ofNat length) i)).toNat =
      (YulSemantics.EVM.byteFrom calldata.toList (offset + i)).toNat *
        256 ^ (BigLoad.loadReverse length i % 32) := by
  let byte := (YulSemantics.EVM.byteFrom calldata.toList (offset + i)).toNat
  have hbyte : byte < 256 := (YulSemantics.EVM.byteFrom calldata.toList
    (offset + i)).toNat_lt
  have hrem : BigLoad.loadReverse length i % 32 < 32 :=
    Nat.mod_lt _ (by omega)
  have hshift : BigLoad.loadShift length i < 256 := by
    unfold BigLoad.loadShift
    omega
  have hresult : byte * 2 ^ BigLoad.loadShift length i < 2 ^ 256 := by
    unfold BigLoad.loadShift
    have hbytePow : byte < 2 ^ 8 := by norm_num; exact hbyte
    calc
      byte * 2 ^ (8 * (BigLoad.loadReverse length i % 32)) <
          2 ^ 8 * 2 ^ (8 * (BigLoad.loadReverse length i % 32)) :=
        Nat.mul_lt_mul_of_pos_right hbytePow (Nat.pow_pos (by omega))
      _ = 2 ^ (8 + 8 * (BigLoad.loadReverse length i % 32)) := by
        rw [← Nat.pow_add]
      _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [loadShiftWord_ofNat length i hlength hi]
  rw [show BigLoad.loadByte calldata offset i = UInt256.ofNat byte by
    apply Challenge.EvmProof.Word.word_ext
    rw [loadByte_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (hbyte.trans (by norm_num))]
    ]
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat
    (hbyte.trans (by norm_num)) hshift hresult]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hresult]
  unfold BigLoad.loadShift
  rw [show 2 ^ (8 * (BigLoad.loadReverse length i % 32)) =
      256 ^ (BigLoad.loadReverse length i % 32) by
    calc
      2 ^ (8 * (BigLoad.loadReverse length i % 32)) =
          (2 ^ 8) ^ (BigLoad.loadReverse length i % 32) :=
        Nat.pow_mul 2 8 _
      _ = 256 ^ (BigLoad.loadReverse length i % 32) := by norm_num]

private theorem partialValue_lt (calldata : ByteArray)
    (offset length i : Nat) (hi : i ≤ length) :
    partialValue calldata offset length i <
      Limbs.radix ^ Limbs.limbCount length := by
  have hprefix := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
    calldata offset i
  have htail : 0 < 256 ^ (length - i) := Nat.pow_pos (by omega)
  have hpartial : partialValue calldata offset length i < 256 ^ length := by
    unfold partialValue
    calc
      Precompile.bytesToNatPadded calldata offset i * 256 ^ (length - i) <
          256 ^ i * 256 ^ (length - i) :=
        Nat.mul_lt_mul_of_pos_right hprefix htail
      _ = 256 ^ length := by rw [← Nat.pow_add]; congr 2; omega
  rw [Limbs.pow_radix]
  exact hpartial.trans_le (Nat.pow_le_pow_right (by omega)
    (Limbs.width_le_limbs length))

private theorem partialValue_succ (calldata : ByteArray)
    (offset length i : Nat) (hi : i < length) :
    partialValue calldata offset length i +
        (YulSemantics.EVM.byteFrom calldata.toList (offset + i)).toNat *
          256 ^ (BigLoad.loadReverse length i % 32) *
          Limbs.radix ^ BigLoad.loadLimb length i =
      partialValue calldata offset length (i + 1) := by
  let reverse := BigLoad.loadReverse length i
  let limb := BigLoad.loadLimb length i
  let rem := reverse % 32
  have hrecompose : 32 * limb + rem = reverse := by
    dsimp [limb, rem, reverse, BigLoad.loadLimb]
    simpa [Nat.mul_comm] using
      (Nat.div_add_mod (BigLoad.loadReverse length i) 32)
  have htail : length - i = reverse + 1 := by
    dsimp only [reverse]
    unfold BigLoad.loadReverse
    omega
  have htailNext : length - (i + 1) = reverse := by
    dsimp only [reverse]
    unfold BigLoad.loadReverse
    omega
  unfold partialValue
  rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
  rw [htail, htailNext, Limbs.radix_eq, ← Nat.pow_mul]
  rw [← hrecompose]
  rw [Nat.pow_succ]
  rw [Nat.pow_add 256 (32 * limb) rem]
  ring

theorem loadMemory_represents_partial (calldata memory : ByteArray)
    (offset dst length i : Nat) (hlength : length < 2 ^ 256)
    (hi : i ≤ length)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hzero : Limbs.Represents memory dst (Limbs.limbCount length) 0) :
    Limbs.Represents
      (BigLoad.loadMemory calldata offset (UInt256.ofNat dst) length i memory)
      dst (Limbs.limbCount length) (partialValue calldata offset length i) := by
  induction i with
  | zero => simpa [BigLoad.loadMemory, partialValue] using hzero
  | succ i ih =>
      have hiStep : i < length := by omega
      have hbefore := ih (by omega)
      let before := BigLoad.loadMemory calldata offset (UInt256.ofNat dst)
        length i memory
      let limb := BigLoad.loadLimb length i
      let rem := BigLoad.loadReverse length i % 32
      let byte := (YulSemantics.EVM.byteFrom calldata.toList (offset + i)).toNat
      let delta := byte * 256 ^ rem
      let high := Precompile.bytesToNatPadded calldata offset i % 256 ^ (31 - rem)
      have hlimb : limb < Limbs.limbCount length := by
        dsimp only [limb]
        unfold BigLoad.loadLimb BigLoad.loadReverse Limbs.limbCount
        omega
      have haddr := loadAt_ofNat dst length i hlength hiStep hfit
      have hidx : limb < (Limbs.memoryLimbs before dst
          (Limbs.limbCount length)).length := by simpa using hlimb
      have hdidx : limb < (Limbs.limbDigits (Limbs.limbCount length)
          (partialValue calldata offset length i)).length := by
        rw [Limbs.length_limbDigits
          (partialValue_lt calldata offset length i (by omega))]
        exact hlimb
      have hloaded :
          (MachineState.readWord before (dst + 32 * limb)).toNat =
            high * 256 ^ (rem + 1) := by
        calc
          (MachineState.readWord before (dst + 32 * limb)).toNat =
              (Limbs.memoryLimbs before dst
                (Limbs.limbCount length))[limb]'hidx := by
            simp [Limbs.memoryLimbs]
          _ = (Limbs.limbDigits (Limbs.limbCount length)
                (partialValue calldata offset length i))[limb]'hdidx := by
            have hopt := congrArg (fun xs : List Nat => xs[limb]?) hbefore.2
            rw [List.getElem?_eq_getElem hidx,
              List.getElem?_eq_getElem hdidx] at hopt
            exact Option.some.inj hopt
          _ = partialValue calldata offset length i / Limbs.radix ^ limb %
                Limbs.radix := by
            have hdigit := getElem_eq_div_mod_ofDigits Limbs.radix
              (Limbs.limbDigits (Limbs.limbCount length)
                (partialValue calldata offset length i)) limb Limbs.radix_pos
              (by
                rw [Limbs.length_limbDigits
                  (partialValue_lt calldata offset length i (by omega))]
                exact hlimb)
              (by
                intro digit hdigit
                exact Limbs.limbDigits_lt hdigit)
            rw [Limbs.value_limbDigits] at hdigit
            exact hdigit
          _ = high * 256 ^ (rem + 1) := by
            simpa [limb, rem, high] using loaded_digit_factor calldata offset
              length i hlength hiStep
      have hbyte : byte < 256 := by
        exact (YulSemantics.EVM.byteFrom calldata.toList (offset + i)).toNat_lt
      have hp : 256 ^ (rem + 1) = 2 ^ (8 * rem + 8) := by
        calc
          256 ^ (rem + 1) = (2 ^ 8) ^ (rem + 1) := by norm_num
          _ = 2 ^ (8 * (rem + 1)) := (Nat.pow_mul 2 8 _).symm
          _ = 2 ^ (8 * rem + 8) := by ring
      have hq : 256 ^ rem = 2 ^ (8 * rem) := by
        calc
          256 ^ rem = (2 ^ 8) ^ rem := by norm_num
          _ = 2 ^ (8 * rem) := (Nat.pow_mul 2 8 _).symm
      have hland : (high * 256 ^ (rem + 1)) &&& delta = 0 := by
        simpa [delta, hp, hq] using land_separated_blocks high byte (8 * rem) hbyte
      have hdelta :
          (UInt256.shiftLeft (BigLoad.loadByte calldata offset i)
            (BigLoad.loadShiftWord (UInt256.ofNat length) i)).toNat = delta := by
        simpa [delta, byte, rem] using shiftedLoadByte_toNat calldata offset
          length i hlength hiStep
      have hlor :
          (UInt256.lor (MachineState.readWord before (dst + 32 * limb))
            (UInt256.shiftLeft (BigLoad.loadByte calldata offset i)
              (BigLoad.loadShiftWord (UInt256.ofNat length) i))).toNat =
            (MachineState.readWord before (dst + 32 * limb)).toNat + delta := by
        rw [Challenge.EvmProof.Word.word_toNat_lor, hdelta, hloaded]
        exact lor_eq_add_of_land_eq_zero
          (by rw [← hloaded]
              exact (MachineState.readWord before (dst + 32 * limb)).val.isLt)
          (by rw [← hdelta]
              exact (UInt256.shiftLeft (BigLoad.loadByte calldata offset i)
                (BigLoad.loadShiftWord (UInt256.ofNat length) i)).val.isLt)
          hland
      have haddFit :
          (MachineState.readWord before (dst + 32 * limb)).toNat + delta <
            2 ^ 256 := by
        rw [← hlor]
        exact (UInt256.lor (MachineState.readWord before (dst + 32 * limb))
          (UInt256.shiftLeft (BigLoad.loadByte calldata offset i)
            (BigLoad.loadShiftWord (UInt256.ofNat length) i))).val.isLt
      have hwrite := value_memoryLimbs_write_add before dst
        (Limbs.limbCount length) limb delta hlimb haddFit
      rw [Limbs.value_of_represents hbefore] at hwrite
      apply (Limbs.represents_iff_value
        (partialValue_lt calldata offset length (i + 1) hi)).2
      rw [← partialValue_succ calldata offset length i hiStep]
      rw [← hwrite]
      simp only [BigLoad.loadMemory]
      rw [haddr, hlor]

theorem loadMemory_represents (calldata memory : ByteArray)
    (offset dst length : Nat) (hlength : length < 2 ^ 256)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hzero : Limbs.Represents memory dst (Limbs.limbCount length) 0) :
    Limbs.Represents
      (BigLoad.loadMemory calldata offset (UInt256.ofNat dst) length length
        memory)
      dst (Limbs.limbCount length)
        (Precompile.bytesToNatPadded calldata offset length) := by
  simpa [partialValue] using loadMemory_represents_partial calldata memory
    offset dst length length hlength (by omega) hfit hzero

theorem loadReturned_represents (s : State) (offset dst length : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hoffset : offset < 2 ^ 256) (hlength : length < 2 ^ 256)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hzero : Limbs.Represents s.memory dst (Limbs.limbCount length) 0) :
    Limbs.Represents
      (BigLoad.loadReturned s (UInt256.ofNat offset) (UInt256.ofNat length)
        (UInt256.ofNat dst) returnDest rest).memory
      dst (Limbs.limbCount length)
        (Precompile.bytesToNatPadded s.executionEnv.calldata offset length) := by
  have hoffsetWord : (UInt256.ofNat offset).toNat = offset := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoffset]
  have hlengthWord : (UInt256.ofNat length).toNat = length := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlength]
  simpa [BigLoad.loadReturned, BigLoad.loadLoop, hoffsetWord, hlengthWord] using
      loadMemory_represents s.executionEnv.calldata s.memory offset dst length
        hlength hfit hzero

end Challenge.Modexp.Submission.Proofs.Bytecode.BigLoadCorrect
