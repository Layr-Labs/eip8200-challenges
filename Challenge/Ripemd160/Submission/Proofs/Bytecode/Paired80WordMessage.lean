import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Message
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordMessage
open EvmSemantics PairedLaneUInt256Bridge Paired80Core Paired80RoundSemantic Paired80WordRound

theorem wordSum_congr (j : Nat) (a b c d k x y : UInt256)
    (h : Paired80Message.Eq112 (bits x) (bits y)) :
    wordSum j a b c d x k = wordSum j a b c d y k := by
  apply bits_injective
  simp only [bits_wordSum, pairedSum, ← normalize_eq_and]
  exact Paired80Message.normalize_add_message _ _ _ _ h

theorem wordStep_congr (j r s : Nat) (k x y : UInt256) (q : WordLane)
    (h : Paired80Message.Eq112 (bits x) (bits y)) :
    wordStep j r s x k q = wordStep j r s y k q := by
  unfold wordStep wordT
  rw [wordSum_congr j q.a q.b q.c q.d k x y h]

theorem wordStep_of_crypto_message (j r s : Nat)
    (hr0 : 0 < r) (hr : r < 17) (hs0 : 0 < s) (hs : s < 17)
    (wl wr kl kr : UInt32) (l q : Paired80CryptoBridge.CryptoLane) (message : UInt256)
    (h : Paired80Message.Eq112 (bits message) (pack wl.toBitVec wr.toBitVec)) :
    wordStep j r s message (word (pack kl.toBitVec kr.toBitVec)) (packCrypto l q) =
      packCrypto (Paired80CryptoBridge.cryptoStep j r wl kl l)
        (Paired80CryptoBridge.cryptoStep (4-j) s wr kr q) := by
  rw [wordStep_congr j r s _ message (word (pack wl.toBitVec wr.toBitVec)) _ h]
  exact wordStep_of_crypto j r s hr0 hr hs0 hs wl wr kl kr l q

#print axioms wordSum_congr
#print axioms wordStep_congr
#print axioms wordStep_of_crypto_message
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordMessage
