import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalPair
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideCoreBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TerminalTail
set_option warningAsError true
set_option maxHeartbeats 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalWord
open EvmSemantics PairedLaneUInt256Bridge Paired80Core Paired80WordRound
open Paired80WordRotate Paired80WordBoolean Paired80Algorithm Paired80Compression
open Paired80CryptoBridge (CryptoLane)
open Table80WideCoreBridge

def raw78 (message k : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, UInt256.add (wideWordShift (wordScale (wordSum 4 q.a q.b q.c q.d message k) upperWord 6) 27) q.e,
    q.b, wideWordShift q.c 22, q.d⟩

def raw79 (message k : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, wideWordShift (wordSum 4 q.a q.b q.c q.d message k) 101,
    q.b, wideWordShift q.c 22, q.d⟩

def repair (q : WordLane) : WordLane := Table80TerminalTail.normalLane q

theorem bits_scaled_shift (x : UInt256) (d n : Nat) (hn : n < 256) :
    bits (wideWordShift (wordScale x upperWord d) n) =
      (Paired80ScaledRotate.scaleHigh (bits x) d * Table80TerminalTranspose.wideFactor) >>> n := by
  rw [bits_wideWordShift _ n hn, bits_wordScale_upper]

theorem bits_rawScaled (message k : UInt256) (q : WordLane) (d n : Nat) (hn : n < 256) :
    bitLane (⟨q.e, UInt256.add (wideWordShift (wordScale (wordSum 4 q.a q.b q.c q.d message k) upperWord d) n) q.e,
      q.b, wideWordShift q.c 22, q.d⟩ : WordLane) =
      (⟨bits q.e, ((Paired80ScaledRotate.scaleHigh (Paired80RoundSemantic.pairedSum 4 (bits q.a)
        (bits q.b) (bits q.c) (bits q.d) (bits message) (bits k)) d * Table80TerminalTranspose.wideFactor) >>> n) + bits q.e,
        bits q.b, (bits q.c * Table80TerminalTranspose.wideFactor) >>> 22, bits q.d⟩ : Paired80RoundSemantic.Lane 256) := by
  simp only [bitLane, bits_add, bits_scaled_shift _ d n hn,
    bits_wideWordShift _ 22 (by decide), bits_wordSum]

theorem bits_raw78 (message k : UInt256) (q : WordLane) :
    bitLane (raw78 message k q) = Table80WideFinalPair.wide78 (bits message) (bits k) (bitLane q) :=
  bits_rawScaled message k q 6 27 (by decide)

theorem bits_raw79 (message k : UInt256) (q : WordLane) :
    bitLane (raw79 message k q) = Table80WideFinalPair.terminal79 (bits message) (bits k) (bitLane q) := by
  simp only [bitLane, raw79, Table80WideFinalPair.terminal79,
    bits_wideWordShift _ 101 (by decide), bits_wideWordShift _ 22 (by decide), bits_wordSum]

theorem low32_bits (x : UInt256) : (low32 x).toBitVec = low (bits x) := by
  change (bits x).setWidth 32 = _
  exact BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 256)

theorem high32_bits (x : UInt256) : (high32 x).toBitVec = high (bits x) := by
  change (bits (UInt256.shiftRight x (UInt256.ofNat 80))).setWidth 32 = _
  rw [bits_shr _ 80 (by decide), BitVec.setWidth_ushiftRight_eq_extractLsb]
  rfl

theorem bits_repair (q : WordLane) :
    bitLane (repair q) = Table80WideFinalPair.repair (bitLane q) := by
  simp only [bitLane, repair, Table80TerminalTail.normalLane, Table80WideFinalPair.repair,
    packed32, bits_word, UInt32.toBitVec_add, low32_bits, high32_bits]

theorem last_two_normalized (l q : CryptoLane) (message78 message79 : UInt256)
    (wl79 wr79 kl78 kr78 kl79 kr79 : UInt32)
    (hm79 : Paired80Message.Eq112 (bits message79) (pack wl79.toBitVec wr79.toBitVec)) :
    Paired80FinalWord.normalizeLane (repair (raw79 message79 (packed32 kl79 kr79)
      (raw78 message78 (packed32 kl78 kr78) (packCrypto l q)))) =
      wordStep 4 6 11 message79 (packed32 kl79 kr79)
        (wordStep 4 5 11 message78 (packed32 kl78 kr78) (packCrypto l q)) := by
  apply bitLane_injective
  rw [Paired80FinalWord.bits_normalizeLane, bits_repair, bits_raw79, bits_raw78,
    bitLane_wordStep, bitLane_wordStep]
  simp only [packCrypto, bitLane_liftLane, packed32, bits_word]
  exact Table80WideFinalPair.last_two_normalized (Paired80CryptoBridge.bits l)
    (Paired80CryptoBridge.bits q) (bits message78) (bits message79)
    wl79.toBitVec wr79.toBitVec kl78.toBitVec kr78.toBitVec kl79.toBitVec kr79.toBitVec hm79

def finish (message : Nat → UInt256) (q : WordLane) : WordLane :=
  raw79 (message 79) (key 79) (raw78 (message 78) (key 78) q)

theorem finish_normalized (message : Nat → UInt256) (words : Nat → UInt32)
    (l q : CryptoLane)
    (hm79 : Paired80Message.Eq112 (bits (message 79))
      (pack (words Crypto.Ripemd160.r[79]!).toBitVec (words Crypto.Ripemd160.rP[79]!).toBitVec)) :
    Paired80FinalWord.normalizeLane (repair (finish message (packCrypto l q))) =
      step 79 (message 79) (step 78 (message 78) (packCrypto l q)) := by
  exact last_two_normalized l q (message 78) (message 79)
    (words Crypto.Ripemd160.r[79]!) (words Crypto.Ripemd160.rP[79]!)
    Crypto.Ripemd160.K[4]! Crypto.Ripemd160.KP[4]!
    Crypto.Ripemd160.K[4]! Crypto.Ripemd160.KP[4]! hm79

theorem finish_fold_normalized (message : Nat → UInt256) (words : Nat → UInt32)
    (l q : CryptoLane) (hm : MessageReady message words 80) :
    Paired80FinalWord.normalizeLane (repair (finish message (fold message 78 (packCrypto l q)))) =
      fold message 80 (packCrypto l q) := by
  change _ = step 79 (message 79) (step 78 (message 78) (fold message 78 (packCrypto l q)))
  rw [fold_crypto message words 78 (by decide) l q (fun i hi => hm i (by omega))]
  exact finish_normalized message words _ _ (hm 79 (by decide))

theorem finish_fold_eq_old (message : Nat → UInt256) (words : Nat → UInt32)
    (l q : CryptoLane) (hm : MessageReady message words 80) :
    Paired80FinalWord.normalizeLane (repair (finish message (fold message 78 (packCrypto l q)))) =
      Paired80FinalWord.normalizeLane (Paired80FinalWord.finish message (fold message 78 (packCrypto l q))) := by
  rw [finish_fold_normalized message words l q hm,
    Paired80FinalWord.finish_fold_normalized message words l q hm]

#print axioms bits_raw78
#print axioms bits_raw79
#print axioms bits_repair
#print axioms last_two_normalized
#print axioms finish_fold_eq_old
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalWord
