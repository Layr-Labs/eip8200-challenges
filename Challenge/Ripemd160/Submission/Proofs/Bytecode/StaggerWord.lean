import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRound
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerWord
open EvmSemantics PairedLaneUInt256Bridge Paired80Core Paired80RoundSemantic
open Paired80WordBoolean Paired80WordRotate Paired80WordRound

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
  all_goals simp only [key, StaggerBoolean.key, Paired80GroupTwoHoist.adjustedConstant,
    h, ite_true, ite_false, bits_add, pairWord, bits_word, bits_ofNat, BitVec.add_assoc]

def sum (mode : Nat) (a b c d message rawKey : UInt256) : UInt256 :=
  UInt256.land (UInt256.add (UInt256.add (UInt256.add a
    (raw mode (selector mode) b c d)) message) rawKey) pairWord

theorem bits_sum (mode : Nat) (a b c d message k : UInt256) :
    bits (sum mode a b c d message (key mode k)) =
      StaggerRound.rawSum mode (bits a) (bits b) (bits c) (bits d) (bits message) (bits k) := by
  simp only [sum, StaggerRound.rawSum, bits_land, bits_add, bits_raw, selector,
    bits_word, bits_key, pairWord, normalize_eq_and]

def t (mode r s : Nat) (message rawKey : UInt256) (q : WordLane) : UInt256 :=
  UInt256.land (UInt256.add (wordRotate (sum mode q.a q.b q.c q.d message rawKey) r s) q.e) pairWord

def step (mode r s : Nat) (message rawKey : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, t mode r s message rawKey q, q.b, UInt256.land (wordShift q.c 22) pairWord, q.d⟩

theorem bitLane_step (mode r s : Nat) (message k : UInt256) (q : WordLane) :
    bitLane (step mode r s message (key mode k) q) =
      StaggerRound.step mode r s (bits message) (bits k) (bitLane q) := by
  cases q
  simp only [step, t, bitLane, StaggerRound.step, StaggerRound.t, bits_land, bits_add,
    bits_wordRotate, bits_sum, bits_wordShift _ 22 (by decide), pairWord, bits_word,
    normalize_eq_and]

theorem step_of_crypto (mode r s : Nat) (hm : mode < 9)
    (hr0 : 0 < r) (hr : r < 17) (hs0 : 0 < s) (hs : s < 17)
    (wl wr kl kr : UInt32) (l q : Paired80CryptoBridge.CryptoLane) (message : UInt256)
    (hmsg : Paired80Message.Eq112 (bits message) (pack wl.toBitVec wr.toBitVec)) :
    step mode r s message (key mode (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) =
      packCrypto (Paired80CryptoBridge.cryptoStep (StaggerBoolean.leftGroup mode) r wl kl l)
        (Paired80CryptoBridge.cryptoStep (StaggerBoolean.rightGroup mode) s wr kr q) := by
  apply bitLane_injective
  rw [bitLane_step]
  simp only [packCrypto, bitLane_liftLane, bits_word]
  rw [StaggerRound.step_pack mode r s hm hr0 hr hs0 hs _ _ _ _ _ _ (bits message) hmsg]
  rw [Paired80CryptoBridge.cryptoStep_bits _ r hr0 hr, Paired80CryptoBridge.cryptoStep_bits _ s hs0 hs]

#print axioms bits_raw
#print axioms bits_key
#print axioms bits_sum
#print axioms bitLane_step
#print axioms step_of_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerWord
