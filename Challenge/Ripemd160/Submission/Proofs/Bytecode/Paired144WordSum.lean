import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordBooleanBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactInput
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordSum
open EvmSemantics Paired144Core Paired144Boolean Paired144WordRound PairedLaneUInt256Bridge
open Paired144WordBooleanBridge

def scalarSum (j : Nat) (a b c d message k : UInt32) : UInt32 :=
  ((a + Crypto.Ripemd160.f j b c d) + message) + k

theorem crypto_f_toBitVec (j : Nat) (b c d : UInt32) :
    (Crypto.Ripemd160.f j b c d).toBitVec =
      f j (BitVec.allOnes 32) b.toBitVec c.toBitVec d.toBitVec :=
  PairedLaneCryptoBridge.crypto_f_toBitVec j b c d

theorem bits_wordSum_pack (j : Nat) (a b c d m k a' b' c' d' m' k' : UInt32) :
    bits (wordSum j (word (pack a.toBitVec a'.toBitVec))
      (word (pack b.toBitVec b'.toBitVec)) (word (pack c.toBitVec c'.toBitVec))
      (word (pack d.toBitVec d'.toBitVec)) (word (pack m.toBitVec m'.toBitVec))
      (word (pack k.toBitVec k'.toBitVec))) =
    ((pack a.toBitVec a'.toBitVec +
      pack (Crypto.Ripemd160.f j b c d).toBitVec (Crypto.Ripemd160.f (4-j) b' c' d').toBitVec) +
      pack m.toBitVec m'.toBitVec) + pack k.toBitVec k'.toBitVec := by
  simp only [wordSum, bits_add, bits_word, bits_booleanPair, pairedF_pack,
    crypto_f_toBitVec]

theorem wordSum_inputs (j : Nat) (l q : CryptoLane) (wl wr kl kr : UInt32) :
    let x := wordSum j (packCrypto l q).a (packCrypto l q).b (packCrypto l q).c
      (packCrypto l q).d (word (pack wl.toBitVec wr.toBitVec)) (word (pack kl.toBitVec kr.toBitVec))
    let a := (scalarSum j l.a l.b l.c l.d wl kl).toBitVec
    let b := (scalarSum (4-j) q.a q.b q.c q.d wr kr).toBitVec
    Paired144CompactInput.compact (bits x) =
      BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< 72) ∧
      normalize (bits x) = pack a b := by
  dsimp only
  rw [show bits (wordSum j (packCrypto l q).a (packCrypto l q).b (packCrypto l q).c
      (packCrypto l q).d (word (pack wl.toBitVec wr.toBitVec)) (word (pack kl.toBitVec kr.toBitVec))) = _ from
    bits_wordSum_pack j l.a l.b l.c l.d wl kl q.a q.b q.c q.d wr kr]
  constructor
  · simpa only [scalarSum, UInt32.toBitVec_add] using
      Paired144CompactInput.compact_four_adds l.a.toBitVec (Crypto.Ripemd160.f j l.b l.c l.d).toBitVec
        wl.toBitVec kl.toBitVec q.a.toBitVec (Crypto.Ripemd160.f (4-j) q.b q.c q.d).toBitVec wr.toBitVec kr.toBitVec
  · simpa only [scalarSum, UInt32.toBitVec_add] using
      Paired144CompactInput.normalize_four_adds l.a.toBitVec (Crypto.Ripemd160.f j l.b l.c l.d).toBitVec
        wl.toBitVec kl.toBitVec q.a.toBitVec (Crypto.Ripemd160.f (4-j) q.b q.c q.d).toBitVec wr.toBitVec kr.toBitVec

#print axioms wordSum_inputs
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordSum
