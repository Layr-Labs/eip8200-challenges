import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalWord
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80LateMask77
open Paired80Core Paired80RoundSemantic Paired80FinalPair Paired80Terminal
open Table80WideFinalPair

theorem suffix_ignore_extra_d (q : Lane 256) (x message78 k78 message79 k79 : BitVec 256)
    (hb : normalize q.b = q.b) (hc : normalize q.c = q.c)
    (hx : normalize x = q.d) (hxgap : x.getLsbD 48 = false)
    (hs : (k78 + (message78 + q.a)).toNat % 2 ^ 80 < 2 ^ 47) :
    normalizeLane (repair (terminal79 message79 k79 (wide78 message78 k78 {q with d := x}))) =
    normalizeLane (repair (terminal79 message79 k79 (wide78 message78 k78 q))) := by
  have hsum : pairedSum 4 q.a q.b q.c x message78 k78 =
      pairedSum 4 q.a q.b q.c q.d message78 k78 := by
    have h := sum4_maskBD {q with d := x} message78 k78 hc (clean_gap q.b hb) hxgap hs
    simpa only [hb, hx] using h
  have hlow : low x = low q.d := by
    simpa only [normalize, low_pack] using congrArg low hx
  have hhigh : high x = high q.d := by
    simpa only [normalize, high_pack] using congrArg high hx
  have hd : normalize q.d = q.d := by
    rw [← hx, normalize_idem]
  simp only [wide78, terminal79, repair, normalizeLane, hsum, hx, hd, hlow, hhigh]

#print axioms suffix_ignore_extra_d

def partial77 (message k : BitVec 256) (q : Lane 256) : Lane 256 :=
  {pairedStep 4 8 13 message k q with
    d := (q.c * Table80TerminalTranspose.wideFactor) >>> 22}

theorem suffix_after_partial77 (l q : Lane 32) (message77 k77 message78 message79 k79 : BitVec 256)
    (wl78 wr78 kl78 kr78 : BitVec 32)
    (hm78 : Paired80Message.Eq112 message78 (pack wl78 wr78)) :
    normalizeLane (repair (terminal79 message79 k79
      (wide78 message78 (pack kl78 kr78) (partial77 message77 k77 (packLane l q))))) =
    normalizeLane (repair (terminal79 message79 k79
      (wide78 message78 (pack kl78 kr78) (pairedStep 4 8 13 message77 k77 (packLane l q))))) := by
  apply suffix_ignore_extra_d
  · simp only [pairedStep, pairedT, ← normalize_eq_and, normalize_idem]
  · exact normalize_pack l.b q.b
  · simpa only [pairedStep, packLane, ← normalize_eq_and] using
      Table80TerminalTranspose.normalize_wide_shift (pack l.c q.c) 22 (by decide)
  · rw [BitVec.getLsbD_ushiftRight, Table80TerminalTranspose.wide_bit _ _ (by decide)]
    exact c10_gap l.c q.c
  · exact three_small _ _ _ (clean_low _ (normalize_pack _ _))
      (message_low message78 wl78 wr78 hm78) (clean_low _ (normalize_pack l.e q.e))

#print axioms suffix_after_partial77


open EvmSemantics PairedLaneUInt256Bridge Paired80WordRound Paired80Algorithm
open Table80WideCoreBridge
open Paired80CryptoBridge (CryptoLane)

def raw77 (message k : UInt256) (q : WordLane) : WordLane :=
  {wordStep 4 8 13 message k q with d := wideWordShift q.c 22}

theorem bits_raw77 (message k : UInt256) (q : WordLane) :
    bitLane (raw77 message k q) = partial77 (bits message) (bits k) (bitLane q) := by
  simp only [raw77, wordStep, bitLane, partial77, pairedStep, bits_wordT,
    bits_wideWordShift _ 22 (by decide)]

theorem suffix_word (l q : CryptoLane) (message77 k77 message78 message79 k79 : UInt256)
    (wl78 wr78 kl78 kr78 : UInt32)
    (hm78 : Paired80Message.Eq112 (bits message78) (pack wl78.toBitVec wr78.toBitVec)) :
    Paired80FinalWord.normalizeLane (Table80WideFinalWord.repair
      (Table80WideFinalWord.raw79 message79 k79
        (Table80WideFinalWord.raw78 message78 (packed32 kl78 kr78)
          (raw77 message77 k77 (packCrypto l q))))) =
    Paired80FinalWord.normalizeLane (Table80WideFinalWord.repair
      (Table80WideFinalWord.raw79 message79 k79
        (Table80WideFinalWord.raw78 message78 (packed32 kl78 kr78)
          (wordStep 4 8 13 message77 k77 (packCrypto l q))))) := by
  apply bitLane_injective
  simp only [Paired80FinalWord.bits_normalizeLane, Table80WideFinalWord.bits_repair,
    Table80WideFinalWord.bits_raw79, Table80WideFinalWord.bits_raw78, bits_raw77,
    bitLane_wordStep, packCrypto, bitLane_liftLane, packed32, bits_word]
  exact suffix_after_partial77 (Paired80CryptoBridge.bits l) (Paired80CryptoBridge.bits q)
    (bits message77) (bits k77) (bits message78) (bits message79) (bits k79)
    wl78.toBitVec wr78.toBitVec kl78.toBitVec kr78.toBitVec hm78

def finish (message : Nat → UInt256) (q : WordLane) : WordLane :=
  Table80WideFinalWord.finish message (raw77 (message 77) (key 77) q)

theorem finish_fold_eq_old (message : Nat → UInt256) (words : Nat → UInt32)
    (l q : CryptoLane) (hm : MessageReady message words 80) :
    Paired80FinalWord.normalizeLane (Table80WideFinalWord.repair
      (finish message (fold message 77 (packCrypto l q)))) =
    Paired80FinalWord.normalizeLane
      (Paired80FinalWord.finish message (fold message 78 (packCrypto l q))) := by
  have h : Paired80FinalWord.normalizeLane (Table80WideFinalWord.repair
      (finish message (fold message 77 (packCrypto l q)))) =
      Paired80FinalWord.normalizeLane (Table80WideFinalWord.repair
        (Table80WideFinalWord.finish message (fold message 78 (packCrypto l q)))) := by
    change Paired80FinalWord.normalizeLane (Table80WideFinalWord.repair
      (finish message (fold message 77 (packCrypto l q)))) =
      Paired80FinalWord.normalizeLane (Table80WideFinalWord.repair
        (Table80WideFinalWord.finish message
          (step 77 (message 77) (fold message 77 (packCrypto l q)))))
    rw [fold_crypto message words 77 (by decide) l q (fun i hi => hm i (by omega))]
    exact suffix_word _ _ (message 77) (key 77) (message 78) (message 79) (key 79)
      (words Crypto.Ripemd160.r[78]!) (words Crypto.Ripemd160.rP[78]!)
      Crypto.Ripemd160.K[4]! Crypto.Ripemd160.KP[4]! (hm 78 (by decide))
  exact h.trans (Table80WideFinalWord.finish_fold_eq_old message words l q hm)

#print axioms bits_raw77
#print axioms suffix_word
#print axioms finish_fold_eq_old

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80LateMask77
