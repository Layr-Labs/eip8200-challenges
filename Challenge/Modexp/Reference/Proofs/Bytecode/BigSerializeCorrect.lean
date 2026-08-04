import Challenge.Modexp.Reference.Proofs.Bytecode.BigCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Functional correctness of multi-limb result serialization -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigSerializeCorrect

open EvmSemantics
open EvmSemantics.EVM

theorem getElem_eq_div_mod_ofDigits (radix : Nat) (digits : List Nat)
    (index : Nat) (hradix : 0 < radix) (hindex : index < digits.length)
    (hdigits : ∀ digit ∈ digits, digit < radix) :
    digits[index] = Nat.ofDigits radix digits / radix ^ index % radix := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop index hradix digits hdigits]
  rw [List.drop_eq_getElem_cons hindex]
  simp only [Nat.ofDigits_cons]
  rw [Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hdigits digits[index] (List.getElem_mem hindex))]

theorem readLimb_of_represents {memory : ByteArray} {ptr count value index : Nat}
    (hrep : Limbs.Represents memory ptr count value) (hindex : index < count) :
    (MachineState.readWord memory (ptr + 32 * index)).toNat =
      value / Limbs.radix ^ index % Limbs.radix := by
  have hget := getElem_eq_div_mod_ofDigits Limbs.radix
    (Limbs.memoryLimbs memory ptr count) index Limbs.radix_pos
    (by simpa using hindex)
    (fun digit hdigit => Limbs.memoryLimb_lt memory ptr count hdigit)
  rw [Limbs.value_of_represents hrep] at hget
  simpa [Limbs.memoryLimbs] using hget

theorem serializerLimb_eq (m k : Nat) (hm : m < 2 ^ 256) (hk : k < m) :
    BigSerialize.serializerLimb m k =
      UInt256.ofNat (BigLoad.loadLimb m k) := by
  change BigLoad.loadLimbWord (UInt256.ofNat m) k = _
  exact BigLoadCorrect.loadLimbWord_ofNat m k hm hk

theorem serializerShift_eq (m k : Nat) (hm : m < 2 ^ 256) (hk : k < m) :
    BigSerialize.serializerShift m k =
      UInt256.ofNat (BigLoad.loadShift m k) := by
  change BigLoad.loadShiftWord (UInt256.ofNat m) k = _
  exact BigLoadCorrect.loadShiftWord_ofNat m k hm hk

theorem extractedLimbByte (value limb rem : Nat) (hrem : rem < 32) :
    ((value / Limbs.radix ^ limb % Limbs.radix) / 256 ^ rem) % 256 =
      value / 256 ^ (32 * limb + rem) % 256 := by
  have hradix : Limbs.radix = 256 ^ 32 := Limbs.radix_eq
  let head := value / 256 ^ (32 * limb)
  have hsplit : 256 ^ 32 = 256 ^ rem * 256 ^ (32 - rem) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hdiv : value / 256 ^ (32 * limb) / 256 ^ rem =
      value / 256 ^ (32 * limb + rem) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [hradix]
  rw [show (256 ^ 32) ^ limb = 256 ^ (32 * limb) by
    rw [Nat.pow_mul]]
  change ((head % 256 ^ 32) / 256 ^ rem) % 256 = _
  rw [hsplit, Nat.mod_mul_right_div_self]
  have hdvd : 256 ∣ 256 ^ (32 - rem) := by
    exact dvd_pow_self 256 (by omega)
  rw [Nat.mod_mod_of_dvd _ hdvd]
  exact congrArg (fun n => n % 256) hdiv

theorem serializedByte_correct (memory : ByteArray) (m k value : Nat)
    (hmBound : m ≤ 1024) (hk : k < m)
    (hrep : Limbs.Represents memory 2048 (Limbs.limbCount m) value) :
    (BigSerialize.serializedByte memory m k).toNat =
      value / 256 ^ (m - 1 - k) % 256 := by
  let reverse := m - 1 - k
  let limb := BigLoad.loadLimb m k
  let rem := BigLoad.loadReverse m k % 32
  have hm : m < 2 ^ 256 := by omega
  have hlimb : limb < Limbs.limbCount m := by
    simp only [limb, BigLoad.loadLimb, BigLoad.loadReverse, Limbs.limbCount]
    omega
  have hn : Limbs.limbCount m ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hrem : rem < 32 := by
    exact Nat.mod_lt _ (by omega)
  have haddr : (UInt256.ofNat 2048 +
      UInt256.shiftLeft (UInt256.ofNat limb) (UInt256.ofNat 5)).toNat =
      2048 + 32 * limb := BigHelpers.addOffset_toNat 2048 limb (by omega)
  have hword := readLimb_of_represents hrep hlimb
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have hshift : BigLoad.loadShift m k = 8 * rem := by
    simp [BigLoad.loadShift, rem]
  have hshiftLt : BigLoad.loadShift m k < 256 := by omega
  have hrecompose : 32 * (reverse / 32) + reverse % 32 = reverse := by
    have h := Nat.mod_add_div reverse 32
    omega
  unfold BigSerialize.serializedByte
  rw [serializerLimb_eq m k hm hk, serializerShift_eq m k hm hk, h2048,
    haddr, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat _ hshiftLt,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 255 < 2 ^ 256)]
  rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [hshift, show 2 ^ (8 * rem) = 256 ^ rem by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, Nat.pow_mul]]
  rw [hword]
  simpa [limb, rem, reverse, BigLoad.loadLimb, BigLoad.loadReverse,
    hrecompose] using
    extractedLimbByte value limb rem hrem

end Challenge.Modexp.Reference.Proofs.Bytecode.BigSerializeCorrect
