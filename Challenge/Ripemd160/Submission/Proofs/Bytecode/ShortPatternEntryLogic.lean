import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Mathlib.Data.Nat.Bitwise
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
open Challenge.Ripemd160 EvmSemantics

/-- The membership bitmap: bit `n - 56` is set exactly for `n ∈ {56, 63, 120}`.
    `2^64 + 2^7 + 1` is `0x010000000000000081`. -/
def sizeBitmap : UInt256 := UInt256.ofNat 18446744073709551745

def sizeFlag (input : ByteArray) : UInt256 :=
  UInt256.isZero (UInt256.land (UInt256.ofNat 1)
    (UInt256.shiftRight sizeBitmap
      (UInt256.sub (UInt256.ofNat input.size) (UInt256.ofNat 56))))

private theorem bitmap_testBit (k : Nat) (hk : k ≠ 0 ∧ k ≠ 7 ∧ k ≠ 64) :
    Nat.testBit 18446744073709551745 k = false := by
  have hsplit : (18446744073709551745 : Nat) = (2 ^ 64 ||| 129) := by decide
  rw [hsplit, Nat.testBit_or, Nat.testBit_two_pow_of_ne (by omega : 64 ≠ k)]
  have h129 : (129 : Nat) = (2 ^ 7 ||| 1) := by decide
  rw [h129, Nat.testBit_or, Nat.testBit_two_pow_of_ne (by omega : 7 ≠ k)]
  have h1 : (1 : Nat) = 2 ^ 0 := by decide
  rw [h1, Nat.testBit_two_pow_of_ne (by omega : 0 ≠ k)]

private theorem bitmap_land_one_zero (k : Nat)
    (hk : k ≠ 0 ∧ k ≠ 7 ∧ k ≠ 64) :
    1 &&& (18446744073709551745 >>> k) = 0 := by
  have ht := bitmap_testBit k hk
  unfold Nat.testBit at ht
  rw [bne_eq_false_iff_eq] at ht
  rw [Nat.and_comm]
  exact ht

theorem sizeFlag_hit (input : ByteArray)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63) :
    sizeFlag input = UInt256.ofNat 0 := by
  rcases hsize with h | h | h <;>
    unfold sizeFlag sizeBitmap <;> rw [h] <;> decide

private theorem shiftWord_ge256_of_small (input : ByteArray)
    (hlt : input.size < 2 ^ 256) (hge : ¬ 56 ≤ input.size) :
    (UInt256.sub (UInt256.ofNat input.size) (UInt256.ofNat 56)).toNat ≥ 256 := by
  rw [Challenge.EvmProof.Word.word_toNat_sub_cond,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 56 < 2 ^ 256),
    if_pos (by omega)]
  omega

private theorem shiftWord_ge256_of_big (input : ByteArray)
    (hlt : input.size < 2 ^ 256) (hge : 56 ≤ input.size)
    (hbig : ¬ input.size - 56 < 256) :
    (UInt256.sub (UInt256.ofNat input.size) (UInt256.ofNat 56)).toNat ≥ 256 := by
  rw [Challenge.EvmProof.Word.word_toNat_sub_cond,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 56 < 2 ^ 256),
    if_neg (by omega)]
  omega

private theorem shiftRight_eq_zero_of_ge256 (v s : UInt256)
    (hs : s.toNat ≥ 256) :
    UInt256.shiftRight v s = UInt256.ofNat 0 := by
  unfold UInt256.shiftRight
  rw [if_pos hs]
  rfl

theorem sizeFlag_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) :
    sizeFlag input = UInt256.ofNat 1 := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hland0 : UInt256.land (UInt256.ofNat 1)
      (UInt256.shiftRight (UInt256.ofNat 18446744073709551745)
        (UInt256.sub (UInt256.ofNat input.size) (UInt256.ofNat 56))) =
      UInt256.ofNat 0 := by
    by_cases hge : 56 ≤ input.size
    · by_cases hbig : input.size - 56 < 256
      · have hsub : UInt256.sub (UInt256.ofNat input.size) (UInt256.ofNat 56) =
            UInt256.ofNat (input.size - 56) :=
          Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) hlt
        apply Challenge.EvmProof.Word.word_ext
        rw [Challenge.EvmProof.Word.word_toNat_land,
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256),
          Nat.mod_eq_of_lt (by norm_num : (0 : Nat) < 2 ^ 256),
          hsub,
          Challenge.EvmProof.Word.shiftRight_ofNat (by norm_num) hbig,
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _)
            (by norm_num : 18446744073709551745 < 2 ^ 256))]
        exact bitmap_land_one_zero (input.size - 56) (by omega)
      · rw [shiftRight_eq_zero_of_ge256 _ _
          (shiftWord_ge256_of_big input hlt hge hbig)]
        decide
    · rw [shiftRight_eq_zero_of_ge256 _ _
        (shiftWord_ge256_of_small input hlt hge)]
      decide
  unfold sizeFlag sizeBitmap
  rw [hland0]
  decide
#print axioms sizeFlag_hit
#print axioms sizeFlag_fail
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
