import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAdaptiveWord

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Congr
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound Paired144Boolean
open Paired144WordRotation
open PairedLaneCryptoBridge (cryptoStep crypto_rotl_toBitVec)

/-! # The JD8 round step: one `jl` bound, nothing else

`StaggerAlgorithm.step_of_crypto` consumes `MessageWord message words i`, i.e. the full
`JunkBound` budget (`jl, jr < 2^64`, plus `jl < 2^35` on compact rounds, `jl < 2^23` / `jl = 0`
on clean words, `jl < 2^32` off words 2 and 14).  JD8 drops eight lane masks, so the junk that
actually arrives is `jl < 2^112 - 4` with `jr` UNBOUNDED.

The proof below does not reprove either dispatch branch.  It reduces the junk case to the clean
case: `normalize` of the physical sum is the same for the dirty message and for the clean packed
message word, every rotation the artifact runs masks with `pairWord` first (so it sees its input
only through `normalize`), and `StaggerAlgorithm.step_of_crypto` is then applied to the clean
word with `jl = jr = 0`.

Sections marked COPIED are verbatim (up to qualification) from the two green standalone files
`evidence/root/rip-jd7-gate/gate.lean` and `evidence/root/rip-jd8-bridge/consumer.lean`; they are
reproduced here because those files are not in the tree and cannot be imported. -/

/-! ## COPIED from gate.lean -- a rotation sees its input only through `normalize`. -/

private theorem wordFusedRotate_congr (x y : UInt256) (r s : Nat)
    (h : UInt256.land x pairWord = UInt256.land y pairWord) :
    wordFusedRotate x r s = wordFusedRotate y r s := by
  unfold wordFusedRotate
  rw [h]

private theorem wordRotate_congr (x y : UInt256) (r s : Nat)
    (h : UInt256.land x pairWord = UInt256.land y pairWord) :
    wordRotate x r s = wordRotate y r s := by
  unfold wordRotate
  by_cases h1 : usesCompact r s
  · rw [if_pos h1, if_pos h1]; exact wordFusedRotate_congr x y r s h
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : usesFusedExtra r s
    · rw [if_pos h2, if_pos h2]; exact wordFusedRotate_congr x y r s h
    · rw [if_neg h2, if_neg h2]
      simp only [h]

private theorem bits_land_pairWord (x : UInt256) :
    bits (UInt256.land x pairWord) = normalize (bits x) := by
  simp only [bits_land, pairWord, bits_word, ← normalize_eq_and]

private theorem wordRotate_of_normalize (x y : UInt256) (r s : Nat)
    (h : normalize (bits x) = normalize (bits y)) :
    wordRotate x r s = wordRotate y r s := by
  refine wordRotate_congr x y r s (bits_injective ?_)
  rw [bits_land_pairWord, bits_land_pairWord, h]

private theorem wordFusedRotate_of_normalize (x y : UInt256) (r s : Nat)
    (h : normalize (bits x) = normalize (bits y)) :
    wordFusedRotate x r s = wordFusedRotate y r s := by
  refine wordFusedRotate_congr x y r s (bits_injective ?_)
  rw [bits_land_pairWord, bits_land_pairWord, h]

/-- ORDINARY / COMPACT / FUSED-EXTRA rounds. -/
theorem staggerWord_t_of_normalize (mode r s : Nat) (message message' rawKey : UInt256)
    (q : WordLane)
    (h : normalize (bits (StaggerWord.sum mode q.a q.b q.c q.d message rawKey))
       = normalize (bits (StaggerWord.sum mode q.a q.b q.c q.d message' rawKey))) :
    StaggerWord.t mode r s message rawKey q = StaggerWord.t mode r s message' rawKey q := by
  unfold StaggerWord.t
  rw [wordRotate_of_normalize _ _ r s h]

theorem staggerWord_step_of_normalize (mode r s : Nat) (message message' rawKey : UInt256)
    (q : WordLane)
    (h : normalize (bits (StaggerWord.sum mode q.a q.b q.c q.d message rawKey))
       = normalize (bits (StaggerWord.sum mode q.a q.b q.c q.d message' rawKey))) :
    StaggerWord.step mode r s message rawKey q = StaggerWord.step mode r s message' rawKey q := by
  unfold StaggerWord.step
  rw [staggerWord_t_of_normalize mode r s message message' rawKey q h]

/-- ADAPTIVE rounds (39, 51, 53, 59): `wordFusedRotate` masks first too. -/
theorem adaptive_t_of_normalize (mode r s : Nat) (message message' rawKey : UInt256)
    (q : WordLane)
    (h : normalize (bits (StaggerWord.sum mode q.a q.b q.c q.d message rawKey))
       = normalize (bits (StaggerWord.sum mode q.a q.b q.c q.d message' rawKey))) :
    StaggerAdaptiveWord.t mode r s message rawKey q
      = StaggerAdaptiveWord.t mode r s message' rawKey q := by
  unfold StaggerAdaptiveWord.t StaggerAdaptiveWord.rotate
  rw [wordFusedRotate_of_normalize _ _ r s h]

theorem adaptive_step_of_normalize (mode r s : Nat) (message message' rawKey : UInt256)
    (q : WordLane)
    (h : normalize (bits (StaggerWord.sum mode q.a q.b q.c q.d message rawKey))
       = normalize (bits (StaggerWord.sum mode q.a q.b q.c q.d message' rawKey))) :
    StaggerAdaptiveWord.step mode r s message rawKey q
      = StaggerAdaptiveWord.step mode r s message' rawKey q := by
  unfold StaggerAdaptiveWord.step
  rw [adaptive_t_of_normalize mode r s message message' rawKey q h]

/-! ## COPIED from consumer.lean -- `normalize` of the physical sum at the wide bound. -/

private theorem low_ofNat (X Y : Nat) :
    low (BitVec.ofNat 256 (X + Y * 2 ^ 144)) = BitVec.ofNat 32 X := by
  apply BitVec.eq_of_toNat_eq
  unfold low
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : 32 ≤ 256)),
    show X + Y * 2 ^ 144 = X + Y * 2 ^ 112 * 2 ^ 32 by rw [Nat.mul_assoc, ← Nat.pow_add],
    Nat.add_mul_mod_self_right]

private theorem high_ofNat (X Y : Nat) (hX : X < 2 ^ 144) :
    high (BitVec.ofNat 256 (X + Y * 2 ^ 144)) = BitVec.ofNat 32 Y := by
  apply BitVec.eq_of_toNat_eq
  unfold high
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hY : Y % 2 ^ 112 + 2 ^ 112 * (Y / 2 ^ 112) = Y := Nat.mod_add_div Y (2 ^ 112)
  have hsplit : X + Y * 2 ^ 144
      = X + Y % 2 ^ 112 * 2 ^ 144 + Y / 2 ^ 112 * 2 ^ 256 := by
    conv_lhs => rw [← hY]
    rw [show (2:Nat) ^ 256 = 2 ^ 112 * 2 ^ 144 by rw [← Nat.pow_add]]
    ring
  rw [hsplit, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (StaggerRound.split_lt X (Y % 2 ^ 112) hX
      (Nat.mod_lt _ (Nat.two_pow_pos 112))),
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos 144), Nat.div_eq_of_lt hX, Nat.zero_add,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : 32 ≤ 112))]

/-- `StaggerRound.normalize_ofNat_junk` with `hB` dropped: `jr` arbitrary. -/
theorem normalize_ofNat_junk_jrfree (A B jl jr : Nat) (hA : A + jl * 2 ^ 32 < 2 ^ 144) :
    normalize (BitVec.ofNat 256 (A + B * 2 ^ 144) + StaggerRound.junk jl jr)
      = normalize (BitVec.ofNat 256 (A + B * 2 ^ 144)) := by
  rw [StaggerRound.ofNat_add_junk]
  have hlo : BitVec.ofNat 32 (A + jl * 2 ^ 32) = BitVec.ofNat 32 A := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  have hhi : BitVec.ofNat 32 (B + jr * 2 ^ 32) = BitVec.ofNat 32 B := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  unfold normalize
  rw [low_ofNat, low_ofNat, high_ofNat _ _ hA, high_ofNat _ _ (by omega : A < 2 ^ 144), hlo, hhi]

/-- The normalize half of `rawSum_inputs_junk`, at the sharp bound, with `jr` free. -/
theorem rawSum_normalize_wide (mode : Nat) (hm : mode < 9)
    (al ar bl br cl cr dl dr wl wr kl kr : BitVec 32) (jl jr : Nat)
    (hjl : jl < 2 ^ 112 - 4) :
    normalize (StaggerRound.rawSum mode (pack al ar) (pack bl br) (pack cl cr) (pack dl dr)
        (pack wl wr + StaggerRound.junk jl jr) (pack kl kr))
      = pack (PairedLaneRoundSemantic.scalarSum (StaggerBoolean.leftGroup mode) al bl cl dl wl kl)
          (PairedLaneRoundSemantic.scalarSum (StaggerBoolean.rightGroup mode) ar br cr dr wr kr) := by
  have h := StaggerRound.rawSum_inputs mode hm al ar bl br cl cr dl dr wl wr kl kr (pack wl wr) rfl
  dsimp only at h
  rw [StaggerRound.rawSum_junk,
    StaggerRound.rawSum_pack mode hm _ _ _ _ _ _ _ _ _ _ _ _ (pack wl wr) rfl]
  rw [StaggerRound.rawSum_pack mode hm _ _ _ _ _ _ _ _ _ _ _ _ (pack wl wr) rfl] at h
  rw [StaggerRound.four_adds_ofNat] at h ⊢
  have hsum : ∀ x y z w : BitVec 32, x.toNat + y.toNat + z.toNat + w.toNat < 2 ^ 34 := by
    intro x y z w
    have := x.isLt; have := y.isLt; have := z.isLt; have := w.isLt
    simp only [Nat.reducePow] at *; omega
  rw [normalize_ofNat_junk_jrfree _ _ _ _
    (by have := hsum al (f (StaggerBoolean.leftGroup mode) (BitVec.allOnes 32) bl cl dl) wl kl
        simp only [Nat.reducePow] at *; omega)]
  exact h.2

theorem sum_normalize_wide (mode : Nat) (hm : mode < 9) (l q : CryptoLane)
    (wl wr kl kr : UInt32) (message : UInt256) (jl jr : Nat)
    (hjl : jl < 2 ^ 112 - 4)
    (hmsg : bits message = pack wl.toBitVec wr.toBitVec + StaggerRound.junk jl jr) :
    normalize (bits (StaggerWord.sum mode (packCrypto l q).a (packCrypto l q).b
        (packCrypto l q).c (packCrypto l q).d message
        (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec)))))
      = pack (Paired144WordSum.scalarSum (StaggerBoolean.leftGroup mode) l.a l.b l.c l.d wl kl).toBitVec
          (Paired144WordSum.scalarSum (StaggerBoolean.rightGroup mode) q.a q.b q.c q.d wr kr).toBitVec := by
  rw [StaggerWord.bits_sum, hmsg]
  simp only [packCrypto, bits_word]
  simpa only [PairedLaneRoundSemantic.scalarSum, Paired144WordSum.scalarSum,
    UInt32.toBitVec_add, PairedLaneCryptoBridge.crypto_f_toBitVec] using
    rawSum_normalize_wide mode hm l.a.toBitVec q.a.toBitVec l.b.toBitVec q.b.toBitVec
      l.c.toBitVec q.c.toBitVec l.d.toBitVec q.d.toBitVec wl.toBitVec wr.toBitVec
      kl.toBitVec kr.toBitVec jl jr hjl

/-! ## NEW: the message word is irrelevant to a round step beyond its `normalize` -/

/-- `StaggerAlgorithm.step` dispatches on `usesAdaptive`; both branches only see the message
word through `normalize` of the physical sum. -/
private theorem junk_zero : StaggerRound.junk 0 0 = 0#256 := rfl

theorem add_junk_zero (v : BitVec 256) : v + StaggerRound.junk 0 0 = v := by
  simp [junk_zero]

#print axioms normalize_ofNat_junk_jrfree
#print axioms rawSum_normalize_wide
#print axioms staggerWord_step_of_normalize
#print axioms adaptive_step_of_normalize
#print axioms sum_normalize_wide
end Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Congr
