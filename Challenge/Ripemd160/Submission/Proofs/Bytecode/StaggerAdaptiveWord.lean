import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144AdaptiveJunk

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAdaptiveWord
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound
open PairedLaneCryptoBridge (cryptoStep crypto_rotl_toBitVec)

def usesAdaptive (r s : Nat) : Prop :=
  (r = 15 ∧ (s = 5 ∨ s = 6)) ∨ (r = 6 ∧ s = 15)
instance (r s : Nat) : Decidable (usesAdaptive r s) := inferInstanceAs (Decidable (_ ∨ _))

def gap (r s : Nat) : Nat := 78 + s - r
def compactWord (g : Nat) (x : UInt256) : UInt256 :=
  UInt256.land (UInt256.lor x (UInt256.shiftRight x (UInt256.ofNat (144 - g))))
    (UInt256.ofNat ((2 ^ 32 - 1) * (1 + 2 ^ g)))
def rotate (x : UInt256) (r s : Nat) : UInt256 :=
  wordShift (compactWord (gap r s) x) (38 - r)
def t (mode r s : Nat) (message rawKey : UInt256) (q : WordLane) : UInt256 :=
  UInt256.land (UInt256.add (rotate (StaggerWord.sum mode q.a q.b q.c q.d message rawKey) r s) q.e) pairWord
def step (mode r s : Nat) (message rawKey : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, t mode r s message rawKey q, q.b, UInt256.land (wordShift q.c 28) pairWord, q.d⟩

theorem cases_of (r s : Nat) (h : usesAdaptive r s) :
    Paired144AdaptiveProduct.Cases (gap r s) (38 - r) r s := by
  rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [Paired144AdaptiveProduct.Cases, gap]

theorem compact_four_junk (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) (jl jr g : Nat)
    (hjr : jr < 2 ^ 64)
    (hg : (g = 68 ∨ g = 69) ∧ jl < 2 ^ 32 ∨ g = 87 ∧ jl = 0) :
    Paired144AdaptiveInput.compact g
      ((((pack a0 b0 + pack a1 b1) + pack a2 b2) + pack a3 b3) + StaggerRound.junk jl jr) =
      BitVec.ofNat 256 ((((a0 + a1) + a2) + a3).toNat) +
        (BitVec.ofNat 256 ((((b0 + b1) + b2) + b3).toNat) <<< g) := by
  rw [StaggerRound.four_adds_ofNat]
  have hb (x y z w : BitVec 32) : x.toNat + y.toNat + z.toNat + w.toNat < 2 ^ 34 := by
    have := x.isLt; have := y.isLt; have := z.isLt; have := w.isLt
    simp only [Nat.reducePow] at *; omega
  rw [Paired144AdaptiveJunk.compact_junk _ _ jl jr g (hb _ _ _ _) (hb _ _ _ _) hjr hg]
  simp only [BitVec.toNat_add, Nat.add_mod_mod, Nat.mod_add_mod]

theorem rawSum_inputs (mode : Nat) (hm : mode < 9)
    (al ar bl br cl cr dl dr wl wr kl kr : BitVec 32) (jl jr g : Nat)
    (hjr : jr < 2 ^ 64)
    (hg : (g = 68 ∨ g = 69) ∧ jl < 2 ^ 32 ∨ g = 87 ∧ jl = 0) :
    let x := StaggerRound.rawSum mode (pack al ar) (pack bl br) (pack cl cr) (pack dl dr)
      (pack wl wr + StaggerRound.junk jl jr) (pack kl kr)
    let a := PairedLaneRoundSemantic.scalarSum (StaggerBoolean.leftGroup mode) al bl cl dl wl kl
    let b := PairedLaneRoundSemantic.scalarSum (StaggerBoolean.rightGroup mode) ar br cr dr wr kr
    Paired144AdaptiveInput.compact g x =
      BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< g) := by
  dsimp only
  rw [StaggerRound.rawSum_junk, StaggerRound.rawSum_pack mode hm _ _ _ _ _ _ _ _ _ _ _ _ (pack wl wr) rfl]
  exact compact_four_junk _ _ _ _ _ _ _ _ jl jr g hjr hg

theorem sum_inputs (mode : Nat) (hm : mode < 9) (l q : CryptoLane)
    (wl wr kl kr : UInt32) (message : UInt256) (jl jr g : Nat)
    (hjr : jr < 2 ^ 64)
    (hg : (g = 68 ∨ g = 69) ∧ jl < 2 ^ 32 ∨ g = 87 ∧ jl = 0)
    (hmsg : bits message = pack wl.toBitVec wr.toBitVec + StaggerRound.junk jl jr) :
    let x := StaggerWord.sum mode (packCrypto l q).a (packCrypto l q).b (packCrypto l q).c
      (packCrypto l q).d message (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec)))
    let a := (Paired144WordSum.scalarSum (StaggerBoolean.leftGroup mode) l.a l.b l.c l.d wl kl).toBitVec
    let b := (Paired144WordSum.scalarSum (StaggerBoolean.rightGroup mode) q.a q.b q.c q.d wr kr).toBitVec
    Paired144AdaptiveInput.compact g (bits x) =
      BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< g) := by
  dsimp only
  rw [StaggerWord.bits_sum, hmsg]
  simp only [packCrypto, bits_word]
  simpa only [PairedLaneRoundSemantic.scalarSum, Paired144WordSum.scalarSum,
    UInt32.toBitVec_add, PairedLaneCryptoBridge.crypto_f_toBitVec] using
    rawSum_inputs mode hm l.a.toBitVec q.a.toBitVec l.b.toBitVec q.b.toBitVec
      l.c.toBitVec q.c.toBitVec l.d.toBitVec q.d.toBitVec wl.toBitVec wr.toBitVec
      kl.toBitVec kr.toBitVec jl jr g hjr hg

theorem bits_compactWord (g : Nat) (x : UInt256) :
    bits (compactWord g x) = Paired144AdaptiveInput.compact g (bits x) := by
  simp only [compactWord, Paired144AdaptiveInput.compact,
    bits_land, bits_lor, bits_shr x (144 - g) (by omega), bits_ofNat]

theorem normalize_rotate_add (x : UInt256) (a b e f : BitVec 32) (r s : Nat)
    (hr : usesAdaptive r s)
    (hc : Paired144AdaptiveInput.compact (gap r s) (bits x) =
      BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< gap r s)) :
    normalize (bits (rotate x r s) + pack e f) = pack (a.rotateLeft r + e) (b.rotateLeft s + f) := by
  rw [rotate, wordShift, bits_shr _ (38 - r) (by omega), bits_mul, bits_compactWord, hc]
  change normalize ((Paired144AdaptiveProduct.fixedProduct a b (gap r s) >>> (38 - r)) + pack e f) = _
  exact Paired144AdaptiveProduct.normalize_shifted_add a b e f _ _ r s (cases_of r s hr)

theorem t_of_crypto (mode r s : Nat) (hm : mode < 9) (hr : usesAdaptive r s)
    (wl wr kl kr : UInt32) (l q : CryptoLane) (message : UInt256) (jl jr : Nat)
    (hjr : jr < 2 ^ 64)
    (hg : (gap r s = 68 ∨ gap r s = 69) ∧ jl < 2 ^ 32 ∨ gap r s = 87 ∧ jl = 0)
    (hmsg : bits message = pack wl.toBitVec wr.toBitVec + StaggerRound.junk jl jr) :
    t mode r s message (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) =
      word (pack
        (Crypto.Ripemd160.rotl32 (Paired144WordSum.scalarSum (StaggerBoolean.leftGroup mode) l.a l.b l.c l.d wl kl) r + l.e).toBitVec
        (Crypto.Ripemd160.rotl32 (Paired144WordSum.scalarSum (StaggerBoolean.rightGroup mode) q.a q.b q.c q.d wr kr) s + q.e).toBitVec) := by
  have hb : 0 < r ∧ r < 32 ∧ 0 < s ∧ s < 32 := by
    rcases hr with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  apply bits_injective
  simp only [t, bits_land, bits_add, pairWord, bits_word, ← normalize_eq_and]
  rw [show bits (packCrypto l q).e = pack l.e.toBitVec q.e.toBitVec from rfl]
  have hinput := sum_inputs mode hm l q wl wr kl kr message jl jr (gap r s) hjr hg hmsg
  have h := normalize_rotate_add _ _ _ l.e.toBitVec q.e.toBitVec r s hr hinput
  simpa only [UInt32.toBitVec_add, crypto_rotl_toBitVec _ r hb.1 hb.2.1,
    crypto_rotl_toBitVec _ s hb.2.2.1 hb.2.2.2] using h

theorem step_of_crypto (mode r s : Nat) (hm : mode < 9) (hr : usesAdaptive r s)
    (wl wr kl kr : UInt32) (l q : CryptoLane) (message : UInt256) (jl jr : Nat)
    (hjr : jr < 2 ^ 64)
    (hg : (gap r s = 68 ∨ gap r s = 69) ∧ jl < 2 ^ 32 ∨ gap r s = 87 ∧ jl = 0)
    (hmsg : bits message = pack wl.toBitVec wr.toBitVec + StaggerRound.junk jl jr) :
    step mode r s message (StaggerWord.key mode (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) =
      packCrypto (cryptoStep (StaggerBoolean.leftGroup mode) r wl kl l)
        (cryptoStep (StaggerBoolean.rightGroup mode) s wr kr q) := by
  unfold step
  rw [t_of_crypto mode r s hm hr wl wr kl kr l q message jl jr hjr hg hmsg,
    show UInt256.land (wordShift (packCrypto l q).c 28) pairWord = _ from
      Paired144WordCrypto.wordCRotate_of_crypto l.c q.c]
  rfl

#print axioms step_of_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAdaptiveWord
