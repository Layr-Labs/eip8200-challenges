import Challenge.EvmProof.Word
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import Mathlib.Tactic
set_option warningAsError true
set_option maxHeartbeats 2000000
open EvmSemantics Challenge.EvmProof
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcSizeGuard
abbrev target : Nat := 5506022574726681700290820341793915503137370776112178186780075461015395893248
theorem sar_negative_ge (v s : UInt256) (hs : s.toNat < 256)
    (hv : 2 ^ 255 ≤ v.toNat) : 2 ^ 255 ≤ (UInt256.sar v s).toNat := by
  unfold UInt256.sar UInt256.toSignedNat UInt256.ofSignedInt
  have hsize : UInt256.size = 2 ^ 256 := rfl
  have hvlt : v.toNat < 2 ^ 256 := v.val.isLt
  rw [if_neg (by omega)]
  simp only [hsize]
  rw [if_neg (by rw [show (2:Nat) ^ 256 / 2 = 2 ^ 255 by norm_num]; omega)]
  rw [Word.word_toNat_ofNat]
  have hd0 : 0 < (2 : Int) ^ s.toNat := by positivity
  have hd1 : 1 ≤ (2 : Int) ^ s.toNat := by omega
  set a : Int := (v.toNat : Int) - ((2 ^ 256 : Nat) : Int)
  set d : Int := (2 : Int) ^ s.toNat
  set q : Int := a / d
  have ha : -(2 ^ 255 : Int) ≤ a ∧ a < 0 := by dsimp [a]; omega
  have hqge : -(2 ^ 255 : Int) ≤ q := by
    dsimp [q]
    apply (Int.le_ediv_iff_mul_le hd0).mpr
    have hm : (-(2 ^ 255 : Int)) * d ≤ (-(2 ^ 255 : Int)) * 1 :=
      mul_le_mul_of_nonpos_left hd1 (by norm_num)
    omega
  have hqneg : q < 0 := by
    dsimp [q]
    exact Int.ediv_neg_of_neg_of_pos ha.2 hd0
  have hmod : q % ((2 ^ 256 : Nat) : Int) = q + 2 ^ 256 := by
    have hdiv : (2 ^ 256 : Int) * (q / (2 ^ 256 : Int)) + q % (2 ^ 256 : Int) = q := Int.mul_ediv_add_emod _ _
    have hqdiv : q / (2 ^ 256 : Int) = -1 := by
      omega
    rw [hqdiv] at hdiv
    omega
  rw [hmod]
  have hn : 2 ^ 255 ≤ (q + (2 ^ 256 : Int)).toNat := by omega
  have hb : (q + (2 ^ 256 : Int)).toNat < 2 ^ 256 := by omega
  rw [Nat.mod_eq_of_lt hb]
  exact hn
theorem sar_positive_div (v s : UInt256) (hs : s.toNat < 256)
    (hv : v.toNat < 2 ^ 255) : (UInt256.sar v s).toNat = v.toNat / 2 ^ s.toNat := by
  unfold UInt256.sar UInt256.toSignedNat UInt256.ofSignedInt
  have hsize : UInt256.size = 2 ^ 256 := rfl
  rw [if_neg (by omega)]
  simp only [hsize]
  rw [if_pos (by rw [show (2:Nat) ^ 256 / 2 = 2 ^ 255 by norm_num]; exact hv)]
  rw [Word.word_toNat_ofNat]
  have hd : 0 < (2 : Int) ^ s.toNat := by positivity
  have hq0 : 0 ≤ (v.toNat : Int) / (2 : Int)^s.toNat := Int.ediv_nonneg (by omega) (by omega)
  have hqle : (v.toNat : Int) / (2 : Int)^s.toNat ≤ v.toNat := by
    apply (Int.ediv_le_iff_le_mul hd).mpr
    have hd1 : 1 ≤ (2 : Int)^s.toNat := by omega
    nlinarith
  rw [Int.emod_eq_of_lt hq0 (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  norm_cast

theorem shift_hit_small (v s : UInt256)
    (heq : (UInt256.sar v s).toNat = target) : s.toNat < 4 := by
  by_cases hs : s.toNat < 256
  · by_cases hv : v.toNat < 2 ^ 255
    · have h := sar_positive_div v s hs hv
      rw [heq] at h
      by_contra hn
      have hd : 16 ≤ 2 ^ s.toNat := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega : 4 ≤ s.toNat)
      have hh := Nat.div_mul_le_self v.toNat (2 ^ s.toNat)
      rw [← h] at hh
      have ht : 0 < target := by decide
      have hm := Nat.mul_le_mul_left target hd
      norm_num [target] at hm hh
      omega
    · have h := sar_negative_ge v s hs (by omega)
      rw [heq] at h
      norm_num [target] at h
  · unfold UInt256.sar at heq
    rw [if_pos (by omega)] at heq
    split_ifs at heq <;> { exfalso; revert heq; decide }
theorem small_shift_prefix (v : UInt256) (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 3)
    (heq : (UInt256.sar v (UInt256.ofNat n)).toNat = target) :
    v.toNat / 2 ^ 232 = if n = 1 then 0x185898 else if n = 2 then 0x30b131 else 0x616263 := by
  let w := v
  have hn4 : n < 4 := by rcases hn with rfl | rfl | rfl <;> omega
  have hs : (UInt256.ofNat n).toNat = n := by rw [Word.word_toNat_ofNat]; omega
  have hw : w.toNat < 2 ^ 255 := by
    by_contra h
    have hh := sar_negative_ge w (UInt256.ofNat n) (by omega) (by omega)
    change (UInt256.sar w (UInt256.ofNat n)).toNat = target at heq
    rw [heq] at hh
    norm_num [target] at hh
  have hdiv := sar_positive_div w (UInt256.ofNat n) (by omega) hw
  rw [heq, hs] at hdiv
  dsimp [w] at hdiv
  rcases hn with rfl | rfl | rfl <;> norm_num [target] at hdiv ⊢ <;> omega
def byte (input : ByteArray) (i : Nat) : UInt8 := YulSemantics.EVM.byteFrom input.toList i

theorem byte_getD (input : ByteArray) (i : Nat) : byte input i = input[i]?.getD 0 := by
  rw [byte, YulEvmCompiler.ByteArray.toList_eq_data]
  simp [YulSemantics.EVM.byteFrom, List.getD_eq_getElem?_getD]
  rfl

theorem prefix_toNat (input : ByteArray) :
    (MachineState.readWord input 0).toNat / 2 ^ 232 =
      (byte input 0).toNat * 65536 + (byte input 1).toNat * 256 + (byte input 2).toNat := by
  have h := Bytes.shiftRight_readWord input 0 3 (by decide) (by decide)
  have hs := Word.shiftRight_toNat (MachineState.readWord input 0) (by decide : 232 < 256)
  rw [h] at hs
  rw [Word.word_toNat_ofNat] at hs
  have hb := Bytes.bytesToNatPadded_lt_pow input 0 3
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hb (by norm_num))] at hs
  rw [← Nat.shiftRight_eq_div_pow, ← hs]
  norm_num [Bytes.bytesToNatPadded_succ, byte, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]

theorem guard_sound (input : ByteArray) (hfit : input.size < 2 ^ 64)
    (heq : (UInt256.sar (MachineState.readWord input 0)
      (UInt256.ofNat input.size)).toNat = target) : input = ByteArray.mk #[97, 98, 99] := by
  have hsmall := shift_hit_small _ _ heq
  have hs : (UInt256.ofNat input.size).toNat = input.size := by rw [Word.word_toNat_ofNat]; omega
  rw [hs] at hsmall
  have hpos : 0 < input.size := by
    by_contra hn
    have hz : input = ByteArray.empty := by
      apply ByteArray.ext_getElem
      · simpa using (show input.size = 0 by omega)
      · intro i hi _; omega
    subst input
    have hzword : MachineState.readWord ByteArray.empty 0 = 0 := by
      unfold MachineState.readWord
      rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList, YulEvmCompiler.ByteArray.toList_eq_data]
      decide
    rw [hzword] at heq
    exfalso
    revert heq
    decide
  have ht := small_shift_prefix (MachineState.readWord input 0) input.size (by omega) heq
  rw [prefix_toNat] at ht
  have b0 := (byte input 0).toNat_lt
  have b1 := (byte input 1).toNat_lt
  have b2 := (byte input 2).toNat_lt
  have hi : input.size = 1 ∨ input.size = 2 ∨ input.size = 3 := by omega
  rcases hi with hn | hn | hn
  · rw [hn] at ht
    have hz1 : byte input 1 = 0 := by rw [byte_getD]; exact Memory.getElem?_getD_eq_zero_of_size_le input 1 (by omega)
    have hz2 : byte input 2 = 0 := by rw [byte_getD]; exact Memory.getElem?_getD_eq_zero_of_size_le input 2 (by omega)
    rw [hz1, hz2] at ht
    norm_num at ht
    omega
  · rw [hn] at ht
    have hz2 : byte input 2 = 0 := by rw [byte_getD]; exact Memory.getElem?_getD_eq_zero_of_size_le input 2 (by omega)
    rw [hz2] at ht
    norm_num at ht
    omega
  · rw [hn] at ht
    norm_num at ht
    have h0 : (byte input 0).toNat = 97 := by omega
    have h1 : (byte input 1).toNat = 98 := by omega
    have h2 : (byte input 2).toNat = 99 := by omega
    apply ByteArray.ext_getElem hn
    intro i hi _
    have hi3 : i < 3 := by omega
    have hb : input[i] = byte input i := by
      rw [byte_getD]
      change input.data[i] = input.data[i]?.getD 0
      rw [Array.getElem?_eq_getElem hi]
      rfl
    rw [hb]
    interval_cases i <;> apply UInt8.ext
    · exact h0
    · exact h1
    · exact h2
end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcSizeGuard
