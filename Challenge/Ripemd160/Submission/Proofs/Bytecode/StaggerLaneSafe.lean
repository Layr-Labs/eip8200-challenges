import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAdaptiveWord

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerLaneSafe
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound

/-- The physical message may contain arbitrary bits between the lanes.  The
lower half retains enough room for the three canonical 32-bit summands. -/
structure Safe (message : UInt256) (lo hi : UInt32) : Prop where
  low : message.toNat % 2^32 = lo.toNat
  high : message.toNat / 2^144 % 2^32 = hi.toNat
  slack : message.toNat % 2^144 + 2^40 ≤ 2^144

theorem normalized_sum (message a b : Nat)
    (hcarry : message % 2^144 + a < 2^144) :
    (message+a+b*2^144)%2^256%2^32 = (message%2^32+a)%2^32 ∧
    ((message+a+b*2^144)%2^256/2^144)%2^32 =
      (message/2^144%2^32+b)%2^32 := by omega

theorem normalize_three (message : BitVec 256)
    (al ar bl br kl kr wl wr : BitVec 32)
    (hlo : message.toNat % 2^32 = wl.toNat)
    (hhi : message.toNat / 2^144 % 2^32 = wr.toNat)
    (hslack : message.toNat % 2^144 + 2^40 ≤ 2^144) :
    normalize (((pack al ar + pack bl br) + message) + pack kl kr) =
      normalize (((pack al ar + pack bl br) + pack wl wr) + pack kl kr) := by
  have ha := al.isLt
  have hb := bl.isLt
  have hk := kl.isLt
  have hcarry : message.toNat % 2^144 + (al.toNat+bl.toNat+kl.toNat) < 2^144 := by
    omega
  have hc := normalized_sum message.toNat (al.toNat+bl.toNat+kl.toNat)
    (ar.toNat+br.toNat+kr.toNat) hcarry
  have hv : (((pack al ar + pack bl br) + message) + pack kl kr).toNat =
      (message.toNat + (al.toNat+bl.toNat+kl.toNat) +
        (ar.toNat+br.toNat+kr.toNat)*2^144)%2^256 := by
    simp only [BitVec.toNat_add, pack_toNat, Nat.mod_add_mod, Nat.add_mod_mod]
    congr 1
    omega
  rw [Paired144CompactInput.normalize_four_adds]
  unfold normalize
  apply congrArg₂ pack
  · apply BitVec.eq_of_toNat_eq
    simp only [low, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hv,
      BitVec.toNat_add, Nat.mod_add_mod, Nat.add_mod_mod]
    rw [hc.1, hlo]
    congr 1
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [high, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, hv,
      BitVec.toNat_add, Nat.mod_add_mod, Nat.add_mod_mod]
    rw [hc.2, hhi]
    congr 1
    omega

theorem sum_normalize (mode : Nat) (hm : mode < 9) (l q : CryptoLane)
    (wl wr kl kr : UInt32) (message : UInt256) (hs : Safe message wl wr) :
    normalize (bits (StaggerWord.sum mode (packCrypto l q).a (packCrypto l q).b
      (packCrypto l q).c (packCrypto l q).d message
      (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec))))) =
    normalize (bits (StaggerWord.sum mode (packCrypto l q).a (packCrypto l q).b
      (packCrypto l q).c (packCrypto l q).d (word (pack wl.toBitVec wr.toBitVec))
      (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec))))) := by
  simp only [StaggerWord.bits_sum, packCrypto, bits_word]
  rw [StaggerRound.rawSum_canonical mode hm, StaggerRound.rawSum_canonical mode hm,
    StaggerBoolean.canonical_pack mode hm]
  exact normalize_three _ _ _ _ _ _ _ _ _ hs.low hs.high hs.slack

theorem sum_mask (mode : Nat) (hm : mode < 9) (l q : CryptoLane)
    (wl wr kl kr : UInt32) (message : UInt256) (hs : Safe message wl wr) :
    UInt256.land (StaggerWord.sum mode (packCrypto l q).a (packCrypto l q).b
      (packCrypto l q).c (packCrypto l q).d message
      (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec)))) pairWord =
    UInt256.land (StaggerWord.sum mode (packCrypto l q).a (packCrypto l q).b
      (packCrypto l q).c (packCrypto l q).d (word (pack wl.toBitVec wr.toBitVec))
      (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec)))) pairWord := by
  apply bits_injective
  simpa only [bits_land, pairWord, bits_word, ← normalize_eq_and] using
    sum_normalize mode hm l q wl wr kl kr message hs

theorem rotate_congr (x y : UInt256) (r s : Nat)
    (h : UInt256.land x pairWord = UInt256.land y pairWord) :
    wordRotate x r s = wordRotate y r s := by
  simp only [wordRotate, wordFusedRotate, h]

theorem step_congr (mode r s : Nat) (hm : mode < 9) (l q : CryptoLane)
    (wl wr kl kr : UInt32) (message : UInt256) (hs : Safe message wl wr) :
    StaggerWord.step mode r s message
      (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) =
    StaggerWord.step mode r s (word (pack wl.toBitVec wr.toBitVec))
      (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) := by
  simp only [StaggerWord.step, StaggerWord.t,
    rotate_congr _ _ r s (sum_mask mode hm l q wl wr kl kr message hs)]

theorem adaptive_step_congr (mode r s : Nat) (hm : mode < 9) (l q : CryptoLane)
    (wl wr kl kr : UInt32) (message : UInt256) (hs : Safe message wl wr) :
    StaggerAdaptiveWord.step mode r s message
      (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) =
    StaggerAdaptiveWord.step mode r s (word (pack wl.toBitVec wr.toBitVec))
      (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) := by
  simp only [StaggerAdaptiveWord.step, StaggerAdaptiveWord.t, StaggerAdaptiveWord.rotate,
    wordFusedRotate, sum_mask mode hm l q wl wr kl kr message hs]

#print axioms normalize_three
#print axioms step_congr
#print axioms adaptive_step_congr
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerLaneSafe
