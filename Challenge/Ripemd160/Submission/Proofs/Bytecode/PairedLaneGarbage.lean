import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRoundSemantic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRound

set_option warningAsError true

/-!
Spacer garbage in the message word is absorbed by the round sum.

The schedule stores each message word with the high half of its 128-bit
slot masked off. That mask is redundant at runtime: the paired lanes sit
at bits [0,32) and [128,160), the three other summands are lane-clean,
and `pairedSum` finishes with `&&& pairMask`. So garbage confined to
bits [32,128) is discarded, provided it cannot carry into bit 128 - and
it cannot, because the lane sums contribute less than 2^34 and the
garbage less than 2^96.

This is the one lemma the mask-removal candidate needs at the spec
level; everything else is plumbing.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore

/-- Spacer garbage in both spacers is absorbed.

`low` garbage sits in bits [32,128) and must stay under `2 ^ 96` so the
low lane cannot carry into bit 128. `high` garbage sits at bit 160 and
above: it is produced when a retained unmasked copy is shifted left by
128 to build the high-lane cell, and it is harmless at any size the
artifact can produce, because carries only travel upwards and `pairMask`
keeps nothing above bit 159. -/
theorem and_four_adds_garbage (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32)
    (low high : Nat) (hlow32 : low % 2 ^ 32 = 0) (hlow : low < 2 ^ 96)
    (hhigh : high < 2 ^ 64) :
    (((pack a0 b0 + pack a1 b1)
        + (pack a2 b2 + BitVec.ofNat 256 (low + high * 2 ^ 160)))
        + pack a3 b3) &&& pairMask =
      pack (((a0 + a1) + a2) + a3) (((b0 + b1) + b2) + b3) := by
  rw [← normalize_eq_and, pack_eq_ofNat a0 b0, pack_eq_ofNat a1 b1,
    pack_eq_ofNat a2 b2, pack_eq_ofNat a3 b3]
  simp only [BitVec.ofNat_add_ofNat]
  have h0 := a0.isLt
  have h1 := a1.isLt
  have h2 := a2.isLt
  have h3 := a3.isLt
  have k0 := b0.isLt
  have k1 := b1.isLt
  have k2 := b2.isLt
  have k3 := b3.isLt
  simp only [Nat.reducePow] at h0 h1 h2 h3 k0 k1 k2 k3 hlow hhigh
  have hsplit :
      (((a0.toNat + b0.toNat * 2 ^ 128) + (a1.toNat + b1.toNat * 2 ^ 128)) +
        ((a2.toNat + b2.toNat * 2 ^ 128) + (low + high * 2 ^ 160))) +
          (a3.toNat + b3.toNat * 2 ^ 128) =
      (a0.toNat + a1.toNat + a2.toNat + a3.toNat + low) +
        (b0.toNat + b1.toNat + b2.toNat + b3.toNat + high * 2 ^ 32) * 2 ^ 128 := by
    simp only [Nat.add_mul]
    omega
  rw [hsplit, normalize_ofNat]
  · -- neither lane moves: both garbage terms are multiples of 2 ^ 32 in
    -- their own half
    have hlo :
        BitVec.ofNat 32 (a0.toNat + a1.toNat + a2.toNat + a3.toNat + low) =
          BitVec.ofNat 32 (a0.toNat + a1.toNat + a2.toNat + a3.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.reducePow]
      omega
    have hhi :
        BitVec.ofNat 32
            (b0.toNat + b1.toNat + b2.toNat + b3.toNat + high * 2 ^ 32) =
          BitVec.ofNat 32 (b0.toNat + b1.toNat + b2.toNat + b3.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.reducePow]
      omega
    rw [hlo, hhi]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [Nat.reducePow] at *
    omega
  · simp only [Nat.reducePow] at *
    omega

#print axioms and_four_adds_garbage

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRoundSemantic

open PairedLaneCore PairedLaneBoolean

/-- `pairedSum` ignores spacer garbage carried in the message word.

This is the form the schedule bridge needs: the stored word may be the
packed pair plus anything confined to bits [32,128), and the round sum
is unchanged. -/
theorem pairedSum_pack_garbage (j : Nat)
    (al ar bl br cl cr dl dr wl wr kl kr : BitVec 32)
    (low high : Nat) (hlow32 : low % 2 ^ 32 = 0) (hlow : low < 2 ^ 96)
    (hhigh : high < 2 ^ 64) :
    pairedSum j (pack al ar) (pack bl br) (pack cl cr) (pack dl dr)
      (pack wl wr + BitVec.ofNat 256 (low + high * 2 ^ 160)) (pack kl kr) =
      pack (scalarSum j al bl cl dl wl kl)
        (scalarSum (4 - j) ar br cr dr wr kr) := by
  unfold pairedSum scalarSum
  rw [pairedF_pack]
  exact and_four_adds_garbage al _ wl kl ar _ wr kr low high hlow32 hlow hhigh

/-- The round transform ignores the same garbage: the message reaches it
only through `pairedSum`. -/
theorem pairedT_garbage (j r s : Nat)
    (al ar bl br cl cr dl dr el er wl wr kl kr : BitVec 32)
    (low high : Nat) (hlow32 : low % 2 ^ 32 = 0) (hlow : low < 2 ^ 96)
    (hhigh : high < 2 ^ 64) :
    pairedT j r s (pack al ar) (pack bl br) (pack cl cr) (pack dl dr)
        (pack el er) (pack wl wr + BitVec.ofNat 256 (low + high * 2 ^ 160))
        (pack kl kr) =
      pairedT j r s (pack al ar) (pack bl br) (pack cl cr) (pack dl dr)
        (pack el er) (pack wl wr) (pack kl kr) := by
  unfold pairedT
  rw [pairedSum_pack_garbage j al ar bl br cl cr dl dr wl wr kl kr
      low high hlow32 hlow hhigh,
    pairedSum_pack j al ar bl br cl cr dl dr wl wr kl kr]

/-- Hence a whole paired round step is unaffected. -/
theorem pairedStep_garbage (j r s : Nat)
    (wl wr kl kr : BitVec 32) (l q : Lane 32)
    (low high : Nat) (hlow32 : low % 2 ^ 32 = 0) (hlow : low < 2 ^ 96)
    (hhigh : high < 2 ^ 64) :
    pairedStep j r s (pack wl wr + BitVec.ofNat 256 (low + high * 2 ^ 160))
        (pack kl kr) (packLane l q) =
      pairedStep j r s (pack wl wr) (pack kl kr) (packLane l q) := by
  cases l
  cases q
  unfold pairedStep packLane
  rw [pairedT_garbage j r s _ _ _ _ _ _ _ _ _ _ wl wr kl kr
      low high hlow32 hlow hhigh]

#print axioms pairedT_garbage
#print axioms pairedStep_garbage

#print axioms pairedSum_pack_garbage

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRoundSemantic

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRound

open EvmSemantics
open PairedLaneCore PairedLaneUInt256Bridge PairedLaneRoundSemantic

/-- The `UInt256`-level round step ignores spacer garbage in the message.

This is `wordStep_of_crypto` with the message word carrying whatever the
unmasked schedule left above the two lanes. -/
theorem wordStep_of_crypto_garbage (j r s : Nat)
    (hr0 : 0 < r) (hr : r < 32) (hs0 : 0 < s) (hs : s < 32)
    (wl wr kl kr : UInt32) (l q : PairedLaneCryptoBridge.CryptoLane)
    (low high : Nat) (hlow32 : low % 2 ^ 32 = 0) (hlow : low < 2 ^ 96)
    (hhigh : high < 2 ^ 64) :
    wordStep j r s
        (UInt256.add (word (pack wl.toBitVec wr.toBitVec))
          (UInt256.ofNat (low + high * 2 ^ 160)))
        (word (pack kl.toBitVec kr.toBitVec)) (packCrypto l q) =
      packCrypto (PairedLaneCryptoBridge.cryptoStep j r wl kl l)
        (PairedLaneCryptoBridge.cryptoStep (4 - j) s wr kr q) := by
  apply bitLane_injective
  rw [bitLane_wordStep]
  simp only [packCrypto, bitLane_liftLane, bits_word]
  rw [bits_add, bits_word, bits_ofNat]
  rw [pairedStep_garbage j r s wl.toBitVec wr.toBitVec kl.toBitVec kr.toBitVec
      (PairedLaneCryptoBridge.bits l) (PairedLaneCryptoBridge.bits q)
      low high hlow32 hlow hhigh]
  exact PairedLaneCryptoBridge.pairedStep_of_crypto j r s hr0 hr hs0 hs
    wl wr kl kr l q

#print axioms wordStep_of_crypto_garbage

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRound
