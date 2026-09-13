import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalPair
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Compression
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalWord
open EvmSemantics PairedLaneUInt256Bridge Paired80Core Paired80WordRound
open Paired80WordRotate Paired80WordBoolean Paired80Algorithm Paired80Compression
open Paired80CryptoBridge (CryptoLane)

def rawStep (r s : Nat) (message k : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, UInt256.add (wordRotate (wordSum 4 q.a q.b q.c q.d message k) r s) q.e,
    q.b, wordShift q.c 22, q.d⟩

def normalizeLane (q : WordLane) : WordLane :=
  ⟨UInt256.land q.a pairWord, UInt256.land q.b pairWord, UInt256.land q.c pairWord,
    UInt256.land q.d pairWord, UInt256.land q.e pairWord⟩

theorem bits_rawStep (r s : Nat) (message k : UInt256) (q : WordLane) :
    bitLane (rawStep r s message k q) =
      Paired80FinalPair.rawStep r s (bits message) (bits k) (bitLane q) := by
  simp only [bitLane, rawStep, Paired80FinalPair.rawStep, bits_add, bits_wordRotate,
    bits_wordSum, bits_wordShift _ 22 (by decide)]

theorem bits_normalizeLane (q : WordLane) :
    bitLane (normalizeLane q) = Paired80FinalPair.normalizeLane (bitLane q) := by
  simp only [bitLane, normalizeLane, Paired80FinalPair.normalizeLane,
    bits_land, pairWord, bits_word, normalize_eq_and]

theorem last_two_normalized (l q : CryptoLane) (message78 message79 : UInt256)
    (wl79 wr79 kl78 kr78 kl79 kr79 : UInt32)
    (hm79 : Paired80Message.Eq112 (bits message79) (pack wl79.toBitVec wr79.toBitVec)) :
    normalizeLane (rawStep 6 11 message79 (packed32 kl79 kr79)
      (rawStep 5 11 message78 (packed32 kl78 kr78) (packCrypto l q))) =
      wordStep 4 6 11 message79 (packed32 kl79 kr79)
        (wordStep 4 5 11 message78 (packed32 kl78 kr78) (packCrypto l q)) := by
  apply bitLane_injective
  rw [bits_normalizeLane, bits_rawStep, bits_rawStep, bitLane_wordStep, bitLane_wordStep]
  simp only [packCrypto, bitLane_liftLane, packed32, bits_word]
  exact Paired80FinalPair.last_two_normalized (Paired80CryptoBridge.bits l)
    (Paired80CryptoBridge.bits q) (bits message78) (bits message79)
    wl79.toBitVec wr79.toBitVec kl78.toBitVec kr78.toBitVec kl79.toBitVec kr79.toBitVec hm79

theorem low32_mask (x : UInt256) : low32 (UInt256.land x pairWord) = low32 x := by
  apply UInt32.eq_of_toBitVec_eq
  change (bits (UInt256.land x pairWord)).setWidth 32 = (bits x).setWidth 32
  rw [bits_land, pairWord, bits_word, ← normalize_eq_and,
    BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 256),
    BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 256)]
  exact low_pack (low (bits x)) (high (bits x))

theorem high32_mask (x : UInt256) : high32 (UInt256.land x pairWord) = high32 x := by
  apply UInt32.eq_of_toBitVec_eq
  change (bits (UInt256.shiftRight (UInt256.land x pairWord) (UInt256.ofNat 80))).setWidth 32 =
    (bits (UInt256.shiftRight x (UInt256.ofNat 80))).setWidth 32
  rw [bits_shr _ 80 (by decide), bits_shr _ 80 (by decide), bits_land, pairWord, bits_word,
    ← normalize_eq_and, BitVec.setWidth_ushiftRight_eq_extractLsb,
    BitVec.setWidth_ushiftRight_eq_extractLsb]
  exact high_pack (low (bits x)) (high (bits x))

theorem combine_normalize (h : Compression.HashState) (q : WordLane) :
    combine h (normalizeLane q) = combine h q := by
  simp only [combine, normalizeLane, unpackLeft, unpackRight, low32_mask, high32_mask]

/-- The physical program deliberately leaves both outputs of each final round unmasked. -/
def finish (message : Nat → UInt256) (q : WordLane) : WordLane :=
  rawStep 6 11 (message 79) (key 79) (rawStep 5 11 (message 78) (key 78) q)

theorem finish_normalized (message : Nat → UInt256) (words : Nat → UInt32)
    (l q : CryptoLane)
    (hm79 : Paired80Message.Eq112 (bits (message 79))
      (pack (words Crypto.Ripemd160.r[79]!).toBitVec (words Crypto.Ripemd160.rP[79]!).toBitVec)) :
    normalizeLane (finish message (packCrypto l q)) =
      step 79 (message 79) (step 78 (message 78) (packCrypto l q)) := by
  exact last_two_normalized l q (message 78) (message 79)
    (words Crypto.Ripemd160.r[79]!) (words Crypto.Ripemd160.rP[79]!)
    Crypto.Ripemd160.K[4]! Crypto.Ripemd160.KP[4]!
    Crypto.Ripemd160.K[4]! Crypto.Ripemd160.KP[4]! hm79

theorem finish_fold_normalized (message : Nat → UInt256) (words : Nat → UInt32)
    (l q : CryptoLane) (hm : MessageReady message words 80) :
    normalizeLane (finish message (fold message 78 (packCrypto l q))) =
      fold message 80 (packCrypto l q) := by
  change _ = step 79 (message 79) (step 78 (message 78) (fold message 78 (packCrypto l q)))
  rw [fold_crypto message words 78 (by decide) l q (fun i hi => hm i (by omega))]
  exact finish_normalized message words _ _ (hm 79 (by decide))

theorem finish_compression (bs : ByteArray) (off : Nat) (h : Compression.HashState)
    (message : Nat → UInt256)
    (hm : MessageReady message (fun k => (CompressionCorrect.schedule bs off)[k]!) 80) :
    CompressionCorrect.hashArray
      (combine h (finish message (fold message 78 (packCrypto
        (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))
        (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h)))))) =
      Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h) bs off := by
  rw [← combine_normalize, finish_fold_normalized message
    (fun k => (CompressionCorrect.schedule bs off)[k]!) _ _ hm]
  exact fold_compression bs off h message hm

#print axioms bits_rawStep
#print axioms last_two_normalized
#print axioms combine_normalize
#print axioms finish_fold_normalized
#print axioms finish_compression
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalWord
