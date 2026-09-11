import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlyData
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlySchedule
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
private theorem readLE32_eq_bytes (bs : ByteArray) (off : Nat) :
    Crypto.Ripemd160.readLE32 bs off =
      let b0 := (bs[off]?.getD 0).toUInt32
      let b1 := (bs[off + 1]?.getD 0).toUInt32
      let b2 := (bs[off + 2]?.getD 0).toUInt32
      let b3 := (bs[off + 3]?.getD 0).toUInt32
      (b0 ||| (b1 <<< UInt32.ofNat 8)) |||
        ((b2 <<< UInt32.ofNat 16) ||| (b3 <<< UInt32.ofNat 24)) := by
  unfold Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [List.range', List.foldl_cons, List.foldl_nil]
  have hbyte (i : Nat) :
      (if h : off + i < bs.size then bs[off + i].toUInt32 else 0) =
        (bs[off + i]?.getD 0).toUInt32 := by
    by_cases h : off + i < bs.size <;> simp [h]
  rw [hbyte 0, hbyte 1, hbyte 2, hbyte 3]
  norm_num
  rw [UInt32.or_assoc]
  rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.shiftLeft_zero]

theorem padded_word_zero (input : ByteArray) (hn : input.size % 64 = 0)
    (k : Nat) (hk : 1 ≤ k ∧ k < 14) :
    Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (input.size + k * 4) = 0 := by
  have hb (j : Nat) (hj : j < 4) :
      (Padding.paddedMessage input)[input.size + k * 4 + j]?.getD 0 = 0 := by
    rw [Nat.add_assoc, padded_byte_aligned input hn (k * 4 + j) (by omega)]
    rw [if_neg (by omega), if_pos (by omega)]
  rw [readLE32_eq_bytes]
  simp only [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide)]
  have h0 := hb 0 (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0]
  decide

theorem padded_word_head (input : ByteArray) (hn : input.size % 64 = 0) :
    Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) input.size = UInt32.ofNat 128 := by
  rw [readLE32_eq_bytes]
  have h0 := padded_byte_aligned input hn 0 (by decide)
  have h1 := padded_byte_aligned input hn 1 (by decide)
  have h2 := padded_byte_aligned input hn 2 (by decide)
  have h3 := padded_byte_aligned input hn 3 (by decide)
  norm_num only at h0 h1 h2 h3
  simp only [Nat.add_zero, ite_true, ite_false] at h0 h1 h2 h3
  rw [h0, h1, h2, h3]
  decide

private theorem assemble_four_bytes (x : Nat) :
    (((UInt8.ofNat (x % 256)).toUInt32 |||
       ((UInt8.ofNat ((x / 2^8) % 256)).toUInt32 <<< UInt32.ofNat 8)) |||
      (((UInt8.ofNat ((x / 2^16) % 256)).toUInt32 <<< UInt32.ofNat 16) |||
       ((UInt8.ofNat ((x / 2^24) % 256)).toUInt32 <<< UInt32.ofNat 24))) = UInt32.ofNat x := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt8.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_mod]
  norm_num only
  rw [show (256 : Nat) = 2^8 by norm_num,
    show (65536 : Nat) = 2^16 by norm_num,
    show (16777216 : Nat) = 2^24 by norm_num,
    show (4294967296 : Nat) = 2^32 by norm_num]
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    Nat.testBit_div_two_pow]
  by_cases hk : k < 32
  · interval_cases k <;> norm_num
  · simp [hk, show ¬ k < 8 by omega]

private theorem padded_footer_byte (input : ByteArray) (hn : input.size % 64 = 0)
    (j : Nat) (hj : j < 8) :
    (Padding.paddedMessage input)[input.size + 56 + j]?.getD 0 =
      UInt8.ofNat (((input.size * 8) / 2 ^ (8 * j)) % 256) := by
  rw [Nat.add_assoc, padded_byte_aligned input hn (56 + j) (by omega)]
  rw [if_neg (by omega), if_neg (by omega)]
  rw [show 56 + j - 56 = j by omega]
  rw [getElem?_pos _ j (by simpa using hj)]
  exact Padding.lengthByte input j hj

theorem padded_word_length_low (input : ByteArray) (hn : input.size % 64 = 0) :
    Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (input.size + 56) =
      UInt32.ofNat (input.size * 8) := by
  rw [readLE32_eq_bytes]
  have h0 := padded_footer_byte input hn 0 (by decide)
  have h1 := padded_footer_byte input hn 1 (by decide)
  have h2 := padded_footer_byte input hn 2 (by decide)
  have h3 := padded_footer_byte input hn 3 (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3]
  simpa only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, pow_zero, Nat.div_one]
    using assemble_four_bytes (input.size * 8)

theorem padded_word_length_high (input : ByteArray) (hn : input.size % 64 = 0) :
    Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (input.size + 60) =
      UInt32.ofNat ((input.size * 8) / 2^32) := by
  rw [readLE32_eq_bytes]
  have h0 := padded_footer_byte input hn 4 (by decide)
  have h1 := padded_footer_byte input hn 5 (by decide)
  have h2 := padded_footer_byte input hn 6 (by decide)
  have h3 := padded_footer_byte input hn 7 (by decide)
  rw [show input.size + 56 + 4 = input.size + 60 by omega] at h0
  rw [show input.size + 56 + 5 = input.size + 60 + 1 by omega] at h1
  rw [show input.size + 56 + 6 = input.size + 60 + 2 by omega] at h2
  rw [show input.size + 56 + 7 = input.size + 60 + 3 by omega] at h3
  rw [h0, h1, h2, h3]
  have h := assemble_four_bytes ((input.size * 8) / 2^32)
  simp only [Nat.div_div_eq_div_mul] at h
  norm_num only at h ⊢
  exact h

#print axioms padded_word_length_low
#print axioms padded_word_length_high

#print axioms assemble_four_bytes

#print axioms padded_word_zero
#print axioms padded_word_head
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlySchedule
