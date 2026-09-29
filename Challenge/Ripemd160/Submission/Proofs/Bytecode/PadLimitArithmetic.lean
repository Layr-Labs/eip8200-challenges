import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
theorem mask_low6_nat (n : Nat) (hn : n < 2 ^ 256) :
    (2 ^ 256 - 1 - 63) &&& n = n >>> 6 <<< 6 := by
  have hm : (2:Nat) ^ 256 - 1 - 63 = (2 ^ 250 - 1) <<< 6 := by
    rw [Nat.shiftLeft_eq]
    have h : (2:Nat) ^ 250 * 2 ^ 6 = 2 ^ 256 := by rw [← pow_add]
    have h2 : (1:Nat) ≤ 2 ^ 250 := Nat.one_le_two_pow
    omega
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases h6 : i ≥ 6
  · by_cases h256 : i < 256
    · rw [show 6 + (i - 6) = i by omega]
      simp [h6, show i - 6 < 250 by omega]
    · have hle : (2:Nat) ^ 256 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hz : n.testBit i = false := Nat.testBit_lt_two_pow (by omega)
      rw [show 6 + (i - 6) = i by omega]
      simp [h6, hz]
  · simp [h6]

theorem land_not63 (x : UInt256) :
    (UInt256.ofNat 63).lnot.land x =
      (x.shiftRight (UInt256.ofNat 6)).shiftLeft (UInt256.ofNat 6) := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have h6 : (UInt256.ofNat 6).toNat = 6 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land]
  unfold UInt256.lnot UInt256.shiftLeft UInt256.shiftRight
  rw [if_neg (by omega : ¬ (UInt256.ofNat 6).toNat ≥ 256)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, h6]
  change ((2 ^ 256 - 1 - (UInt256.ofNat 63).toNat) % 2 ^ 256) &&& x.toNat
      = ((⟨x.val >>> (UInt256.ofNat 6).val⟩ : UInt256).toNat <<< 6) % 2 ^ 256 % 2 ^ 256
  have h63 : (UInt256.ofNat 63).toNat = 63 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num
  have hsr : (⟨x.val >>> (UInt256.ofNat 6).val⟩ : UInt256).toNat = x.toNat >>> 6 := by
    show (x.val >>> (UInt256.ofNat 6).val).val = _
    rw [Fin.shiftRight_val]
    congr 1
  have hbound : x.toNat >>> 6 <<< 6 < 2 ^ 256 := by
    have : x.toNat >>> 6 <<< 6 ≤ x.toNat := by
      rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      exact Nat.div_mul_le_self _ _
    omega
  rw [h63, hsr, Nat.mod_eq_of_lt (by omega : (2:Nat) ^ 256 - 1 - 63 < 2 ^ 256),
    Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt hbound]
  exact mask_low6_nat x.toNat hx

theorem land_not63_mirrored (x : UInt256) :
    x.land (UInt256.ofNat 63).lnot =
      (x.shiftRight (UInt256.ofNat 6)).shiftLeft (UInt256.ofNat 6) := by
  rw [RawExpressionAC.land_comm]
  exact land_not63 x


def rounded (limit : UInt256) : UInt256 :=
  (UInt256.ofNat 63).lnot.land (limit + UInt256.ofNat 72)

theorem rounded_input (input : ByteArray) :
    rounded (UInt256.ofNat input.size) = Padding.paddedWord input := by
  rw [rounded, land_not63]
  rfl

theorem or63_nat (x : Nat) : x ||| 63 = x / 64 * 64 + 63 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h63 : (63:Nat) = 2^6 - 1 := by norm_num
  have hr : x / 64 * 64 + 63 = 2^6 * (x / 2^6) + (2^6 - 1) := by
    rw [show (2:Nat)^6 = 64 by rfl]; omega
  rw [hr, Nat.testBit_or, h63, Nat.testBit_two_pow_mul_add _ (by norm_num : 2^6 - 1 < 2^6),
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 6
  · simp [hi]
  · simp only [hi, if_false, decide_false, Bool.or_false]
    rw [Nat.testBit_div_two_pow, show i - 6 + 6 = i by omega]

theorem coldRounded_eq (n : Nat) (hn : n < 2^64) :
    (UInt256.ofNat 63).lor (UInt256.ofNat 1032 + UInt256.ofNat n) =
      UInt256.ofNat (1023 + Padding.paddedLength n) := by
  have hs : 1032 + n < 2^256 := by
    have : (2:Nat)^64 + 1032 < 2^256 := by norm_num
    omega
  rw [Word.ofNat_add_ofNat hs]
  apply Word.word_ext
  rw [Word.word_toNat_lor, Word.word_toNat_ofNat, Word.word_toNat_ofNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (by norm_num : (63:Nat) < 2^256)]
  unfold Padding.paddedLength
  have hb : 1023 + (n + 72) / 64 * 64 < 2^256 := by
    have : (2:Nat)^64 + 2000 < 2^256 := by norm_num
    have : (n + 72) / 64 * 64 ≤ n + 72 := Nat.div_mul_le_self _ _
    omega
  rw [Nat.mod_eq_of_lt hb, Nat.or_comm, or63_nat]
  omega

/-- The partial-block route writes `(size + 1032) | 63 = 1023 + paddedLength size` into the limit
slot: strictly between the last block pointer and the padded end, and never equal to a block
pointer, so the loop stops after the last padded block and the dispatch never takes the
aligned-padding route. -/
def coldRounded (size : UInt256) : UInt256 :=
  (UInt256.ofNat 63).lor (UInt256.ofNat 1032 + size)

theorem coldRounded_input (input : ByteArray) (hfit : input.size < 2^64) :
    coldRounded (UInt256.ofNat input.size) = UInt256.ofNat (1023 + Padding.paddedLength input.size) :=
  coldRounded_eq input.size hfit

theorem footer_addr (input : ByteArray) (hfit : input.size < 2^64) :
    UInt256.ofNat (1023 + Padding.paddedLength input.size) + UInt256.ofNat 25 =
      Padding.paddedWord input + UInt256.ofNat 1048 := by
  have hp := Padding.paddedLength_lt input.size
  have hs1 : 1023 + Padding.paddedLength input.size + 25 < 2^256 := by
    have : (2:Nat)^64 + 2000 < 2^256 := by norm_num
    omega
  have hs2 : Padding.paddedLength input.size + 1048 < 2^256 := by
    have : (2:Nat)^64 + 2000 < 2^256 := by norm_num
    omega
  rw [Padding.paddedWord_eq input hfit, Word.ofNat_add_ofNat hs1, Word.ofNat_add_ofNat hs2]
  congr 1
  omega

#print axioms rounded_input
#print axioms coldRounded_input
#print axioms footer_addr
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
