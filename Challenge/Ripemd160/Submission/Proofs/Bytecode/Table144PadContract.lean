import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144PadWords
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Pad
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Pad
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PairedScheduleData

theorem lowLength_ofNat (n : Nat) (hn : n < 2^64) :
    lowLength (UInt256.ofNat n) = Word.ofUInt32 (UInt32.ofNat (n * 8)) := by
  unfold lowLength
  rw [Word.shiftLeft_ofNat (by omega) (by decide) (by norm_num; omega)]
  apply Word.word_ext
  rw [Word.word_toNat_land, Word.word_toNat_ofNat, Word.word_toNat_ofNat,
    Word.ofUInt32_toNat, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by decide : 0xffffffff < 2^256),
    Nat.mod_eq_of_lt (by norm_num; omega : n * 2^3 < 2^256)]
  rw [Nat.and_comm, show (4294967295 : Nat) = 2^32-1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem highLength_ofNat (n : Nat) (hn : n < 2^64) :
    highLength (UInt256.ofNat n) = Word.ofUInt32 (UInt32.ofNat ((n * 8) / 2^32)) := by
  unfold highLength
  rw [Word.shiftRight_ofNat (by omega) (by decide)]
  apply Word.word_ext
  rw [Word.word_toNat_land, Word.word_toNat_ofNat, Word.word_toNat_ofNat,
    Word.ofUInt32_toNat, UInt32.toNat_ofNat']
  rw [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by decide : 0xffffffff < 2^256),
    Nat.mod_eq_of_lt (by omega : n / 2^29 < 2^256)]
  rw [Nat.and_comm, show (4294967295 : Nat) = 2^32-1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  congr 1
  omega

theorem padWords_eq_cryptoWords (input : ByteArray) (hfit : input.size < 2^64)
    (hn : input.size % 64 = 0) (k : Nat) (hk : k < 16) :
    Word.ofUInt32 (Crypto.Ripemd160.readLE32 (Padding.paddedMessage input)
      (input.size + k*4)) = padWords (UInt256.ofNat input.size) k := by
  by_cases h0 : k = 0
  · subst k
    simp only [Nat.zero_mul, Nat.add_zero, padded_word_head input hn, padWords, ite_true]
    rfl
  by_cases h14 : k = 14
  · subst k
    simp only [show (14:Nat)*4=56 by decide, padded_word_length_low input hn,
      padWords, if_neg (by decide : ¬ (14:Nat)=0), ite_true]
    exact (lowLength_ofNat input.size hfit).symm
  by_cases h15 : k = 15
  · subst k
    simp only [show (15:Nat)*4=60 by decide, padded_word_length_high input hn,
      padWords, if_neg (by decide : ¬ (15:Nat)=0), if_neg (by decide : ¬ (15:Nat)=14), ite_true]
    exact (highLength_ofNat input.size hfit).symm
  rw [padded_word_zero input hn k (by omega)]
  simp only [padWords, if_neg h0, if_neg h14, if_neg h15]
  rfl

theorem extracted_words (memory : ByteArray) (input : ByteArray) (p : Nat)
    (hfit : input.size < 2^64) (hn : input.size % 64 = 0)
    (hbound : p + 64 < 2^256)
    (hblock : ScheduleCorrect.MessageBlockAt memory (UInt256.ofNat p)
      (Padding.paddedMessage input) input.size) (k : Nat) (hk : k < 16) :
    PairedScheduleData.extractedWord memory p k = padWords (UInt256.ofNat input.size) k := by
  rw [PairedScheduleData.extractedWord_eq_expectedWord memory p k hk hbound, hblock k hk]
  exact padWords_eq_cryptoWords input hfit hn k hk


#print axioms extracted_words
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Pad
