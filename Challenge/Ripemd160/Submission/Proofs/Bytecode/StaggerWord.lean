import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordCrypto
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerWord
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound
open Paired144WordRotation
open PairedLaneCryptoBridge (cryptoStep crypto_rotl_toBitVec)

def raw (mode : Nat) (selector b c d : UInt256) : UInt256 :=
  match mode with
  | 0 => (UInt256.xor (UInt256.xor (UInt256.xor b c) selector) (UInt256.lor d (UInt256.land c selector)))
  | 1 => (UInt256.lor (UInt256.land b c) (UInt256.xor d (UInt256.land (UInt256.xor b selector) (UInt256.lor c d))))
  | 2 => (UInt256.xor (UInt256.lor b (UInt256.lnot c)) d)
  | 3 => (UInt256.xor c (UInt256.land (UInt256.xor d (UInt256.land c selector)) (UInt256.xor b (UInt256.lor c selector))))
  | 4 => (UInt256.xor (UInt256.xor (UInt256.xor b c) selector) (UInt256.lor d (UInt256.land c selector)))
  | 5 => (UInt256.xor b (UInt256.xor d (UInt256.lor (UInt256.land d selector) (UInt256.xor c (UInt256.land b selector)))))
  | 6 => (UInt256.xor d (UInt256.xor selector (UInt256.land (UInt256.xor b selector) (UInt256.xor c (UInt256.land b d)))))
  | 7 => (UInt256.lnot (UInt256.xor b (UInt256.xor d (UInt256.lor (UInt256.xor b selector) (UInt256.xor c (UInt256.land b d))))))
  | _ => (UInt256.xor c (UInt256.xor (UInt256.land b selector) (UInt256.land d (UInt256.lor selector (UInt256.xor b c)))))

theorem bits_raw (mode : Nat) (selector b c d : UInt256) :
    bits (raw mode selector b c d) =
      StaggerBoolean.raw mode pairMask (bits selector) (bits b) (bits c) (bits d) := by
  rcases Nat.lt_or_ge mode 8 with hm | hm
  · interval_cases mode <;> simp only [raw, StaggerBoolean.raw, bits_lnot, bits_land, bits_xor, bits_lor]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    simp only [Nat.add_comm 8 n, raw, StaggerBoolean.raw, bits_lnot, bits_land, bits_xor, bits_lor]

def selector (mode : Nat) : UInt256 := word (StaggerBoolean.selector mode)
def key (mode : Nat) (k : UInt256) : UInt256 :=
  if mode = 2 ∨ mode = 7 then UInt256.add k (UInt256.add pairWord (UInt256.ofNat 1)) else k

theorem bits_key (mode : Nat) (k : UInt256) :
    bits (key mode k) = StaggerBoolean.key mode pairMask (bits k) := by
  by_cases h : mode = 2 ∨ mode = 7
  all_goals simp only [key, StaggerBoolean.key, PairedLaneGroupTwoHoist.adjustedConstant,
    h, ite_true, ite_false, bits_add, pairWord, bits_word, bits_ofNat, BitVec.add_assoc]

def sum (mode : Nat) (a b c d message rawKey : UInt256) : UInt256 :=
  UInt256.add (UInt256.add (UInt256.add a
    (raw mode (selector mode) b c d)) message) rawKey

theorem bits_sum (mode : Nat) (a b c d message k : UInt256) :
    bits (sum mode a b c d message (key mode k)) =
      StaggerRound.rawSum mode (bits a) (bits b) (bits c) (bits d) (bits message) (bits k) := by
  simp only [sum, StaggerRound.rawSum, bits_land, bits_add, bits_raw, selector,
    bits_word, bits_key, pairWord]

def t (mode r s : Nat) (message rawKey : UInt256) (q : WordLane) : UInt256 :=
  UInt256.land (UInt256.add (wordRotate (sum mode q.a q.b q.c q.d message rawKey) r s) q.e) pairWord

def step (mode r s : Nat) (message rawKey : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, t mode r s message rawKey q, q.b, UInt256.land (wordShift q.c 28) pairWord, q.d⟩

theorem sum_inputs (mode : Nat) (hm : mode < 9) (l q : CryptoLane)
    (wl wr kl kr : UInt32) (message : UInt256)
    (hmsg : bits message = pack wl.toBitVec wr.toBitVec) :
    let x := sum mode (packCrypto l q).a (packCrypto l q).b (packCrypto l q).c
      (packCrypto l q).d message (key mode (word (pack kl.toBitVec kr.toBitVec)))
    let a := (Paired144WordSum.scalarSum (StaggerBoolean.leftGroup mode) l.a l.b l.c l.d wl kl).toBitVec
    let b := (Paired144WordSum.scalarSum (StaggerBoolean.rightGroup mode) q.a q.b q.c q.d wr kr).toBitVec
    Paired144CompactInput.compact (bits x) = BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< 72) ∧
      normalize (bits x) = pack a b := by
  dsimp only
  rw [bits_sum]
  simp only [packCrypto, bits_word]
  simpa only [PairedLaneRoundSemantic.scalarSum, Paired144WordSum.scalarSum,
    UInt32.toBitVec_add, PairedLaneCryptoBridge.crypto_f_toBitVec] using
    StaggerRound.rawSum_inputs mode hm l.a.toBitVec q.a.toBitVec l.b.toBitVec q.b.toBitVec
      l.c.toBitVec q.c.toBitVec l.d.toBitVec q.d.toBitVec wl.toBitVec wr.toBitVec
      kl.toBitVec kr.toBitVec (bits message) hmsg

theorem t_of_crypto (mode r s : Nat) (hm : mode < 9)
    (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (wl wr kl kr : UInt32) (l q : CryptoLane) (message : UInt256)
    (hmsg : bits message = pack wl.toBitVec wr.toBitVec) :
    t mode r s message (key mode (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) =
      word (pack
        (Crypto.Ripemd160.rotl32 (Paired144WordSum.scalarSum (StaggerBoolean.leftGroup mode) l.a l.b l.c l.d wl kl) r + l.e).toBitVec
        (Crypto.Ripemd160.rotl32 (Paired144WordSum.scalarSum (StaggerBoolean.rightGroup mode) q.a q.b q.c q.d wr kr) s + q.e).toBitVec) := by
  apply bits_injective
  simp only [t,bits_land,bits_add,pairWord,bits_word,←normalize_eq_and]
  rw [show bits (packCrypto l q).e = pack l.e.toBitVec q.e.toBitVec from rfl]
  have hinput := sum_inputs mode hm l q wl wr kl kr message hmsg
  have h := normalize_rotate_add _ _ _ l.e.toBitVec q.e.toBitVec r s hr0 hr hs0 hs hinput.1 hinput.2
  simpa only [UInt32.toBitVec_add,crypto_rotl_toBitVec _ r (by omega) (by omega),
    crypto_rotl_toBitVec _ s (by omega) (by omega)] using h

theorem step_of_crypto (mode r s : Nat) (hm : mode < 9)
    (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (wl wr kl kr : UInt32) (l q : CryptoLane) (message : UInt256)
    (hmsg : bits message = pack wl.toBitVec wr.toBitVec) :
    step mode r s message (key mode (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) =
      packCrypto (cryptoStep (StaggerBoolean.leftGroup mode) r wl kl l)
        (cryptoStep (StaggerBoolean.rightGroup mode) s wr kr q) := by
  unfold step
  rw [t_of_crypto mode r s hm hr0 hr hs0 hs wl wr kl kr l q message hmsg,
    show UInt256.land (wordShift (packCrypto l q).c 28) pairWord = _ from
      Paired144WordCrypto.wordCRotate_of_crypto l.c q.c]
  rfl

#print axioms bits_raw
#print axioms bits_key
#print axioms bits_sum
#print axioms sum_inputs
#print axioms t_of_crypto
#print axioms step_of_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerWord
