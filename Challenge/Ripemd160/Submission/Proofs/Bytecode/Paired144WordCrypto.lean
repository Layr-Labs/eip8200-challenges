import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRotation
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordGroupTwo
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordCrypto
open EvmSemantics Paired144Core Paired144WordRound PairedLaneUInt256Bridge
open Paired144WordSum Paired144WordRotation
open PairedLaneCryptoBridge (cryptoStep crypto_rotl_toBitVec)

theorem wordT_of_crypto (j r s : Nat) (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (wl wr kl kr : UInt32) (l q : CryptoLane) :
    wordT j r s (packCrypto l q).a (packCrypto l q).b (packCrypto l q).c
      (packCrypto l q).d (packCrypto l q).e
      (word (pack wl.toBitVec wr.toBitVec)) (word (pack kl.toBitVec kr.toBitVec)) =
    word (pack (Crypto.Ripemd160.rotl32 (scalarSum j l.a l.b l.c l.d wl kl) r + l.e).toBitVec
      (Crypto.Ripemd160.rotl32 (scalarSum (4-j) q.a q.b q.c q.d wr kr) s + q.e).toBitVec) := by
  apply bits_injective
  simp only [wordT,bits_land,bits_add,pairWord,bits_word,←normalize_eq_and]
  rw [show bits (packCrypto l q).e = pack l.e.toBitVec q.e.toBitVec from rfl]
  have hinput := wordSum_inputs j l q wl wr kl kr
  have h := normalize_rotate_add _ _ _ l.e.toBitVec q.e.toBitVec r s hr0 hr hs0 hs hinput.1 hinput.2
  simpa only [UInt32.toBitVec_add,crypto_rotl_toBitVec _ r (by omega) (by omega),
    crypto_rotl_toBitVec _ s (by omega) (by omega)] using h

theorem wordCRotate_of_crypto (a b : UInt32) :
    UInt256.land (wordShift (word (pack a.toBitVec b.toBitVec)) 28) pairWord =
      word (pack (Crypto.Ripemd160.rotl32 a 10).toBitVec (Crypto.Ripemd160.rotl32 b 10).toBitVec) := by
  apply bits_injective
  simp only [bits_land,pairWord,bits_word,←normalize_eq_and]
  simpa only [crypto_rotl_toBitVec _ 10 (by decide) (by decide)] using
    normalize_wordShift28 a.toBitVec b.toBitVec

theorem wordStep_of_crypto (j r s : Nat) (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (wl wr kl kr : UInt32) (l q : CryptoLane) :
    wordStep j r s (word (pack wl.toBitVec wr.toBitVec))
        (word (pack kl.toBitVec kr.toBitVec)) (packCrypto l q) =
      packCrypto (cryptoStep j r wl kl l) (cryptoStep (4-j) s wr kr q) := by
  unfold wordStep
  rw [wordT_of_crypto j r s hr0 hr hs0 hs wl wr kl kr l q,
    show UInt256.land (wordShift (packCrypto l q).c 28) pairWord = _ from
      wordCRotate_of_crypto l.c q.c]
  rfl

theorem rawWordStep2_of_crypto (r s : Nat) (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (wl wr kl kr : UInt32) (l q : CryptoLane) :
    rawWordStep2 r s (word (pack wl.toBitVec wr.toBitVec))
        (adjustedK (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) =
      packCrypto (cryptoStep 2 r wl kl l) (cryptoStep 2 s wr kr q) := by
  obtain ⟨hb,hc,hd⟩ := Paired144WordGroupTwo.packCrypto_supported l q
  exact (Paired144WordGroupTwo.rawWordStep2_eq r s _ _ _ hb hc hd).trans
    (wordStep_of_crypto 2 r s hr0 hr hs0 hs wl wr kl kr l q)

#print axioms wordT_of_crypto
#print axioms wordStep_of_crypto
#print axioms rawWordStep2_of_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordCrypto
