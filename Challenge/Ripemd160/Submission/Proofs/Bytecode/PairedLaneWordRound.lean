import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRotate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCryptoBridge

set_option warningAsError true

/-! Canonical UInt256 expressions for the frozen paired round, including its
masked-NOT and equal-rotation variants. This is not an EVM execution trace. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRound

open EvmSemantics
open PairedLaneCore PairedLaneBoolean PairedLaneProduct PairedLaneRoundSemantic
open PairedLaneUInt256Bridge PairedLaneWordBoolean PairedLaneWordRotate

def wordSum (j : Nat) (a b c d message k : UInt256) : UInt256 :=
  UInt256.land (UInt256.add (UInt256.add (UInt256.add a (booleanPair j b c d)) message) k) pairWord

theorem bits_wordSum (j : Nat) (a b c d message k : UInt256) :
    bits (wordSum j a b c d message k) =
      pairedSum j (bits a) (bits b) (bits c) (bits d) (bits message) (bits k) := by
  simp only [wordSum, pairedSum, bits_land, bits_add, bits_booleanPair, pairWord, bits_word]

#print axioms bits_wordSum

def wordT (j r s : Nat) (a b c d e message k : UInt256) : UInt256 :=
  UInt256.land (UInt256.add (wordRotate (wordSum j a b c d message k) r s) e) pairWord

theorem bits_wordT (j r s : Nat) (a b c d e message k : UInt256) :
    bits (wordT j r s a b c d e message k) =
      pairedT j r s (bits a) (bits b) (bits c) (bits d) (bits e) (bits message) (bits k) := by
  simp only [wordT, pairedT, bits_land, bits_add, bits_wordRotate, bits_wordSum,
    pairWord, bits_word]

#print axioms bits_wordT

structure WordLane where
  a : UInt256
  b : UInt256
  c : UInt256
  d : UInt256
  e : UInt256

def bitLane (q : WordLane) : Lane 256 := ⟨bits q.a, bits q.b, bits q.c, bits q.d, bits q.e⟩
def liftLane (q : Lane 256) : WordLane := ⟨word q.a, word q.b, word q.c, word q.d, word q.e⟩

theorem bitLane_liftLane (q : Lane 256) : bitLane (liftLane q) = q := rfl

theorem bitLane_injective : Function.Injective bitLane := by
  intro a b h
  exact congrArg liftLane h

#print axioms bitLane_injective

def wordStep (j r s : Nat) (message k : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, wordT j r s q.a q.b q.c q.d q.e message k, q.b,
    UInt256.land (wordShift q.c 22) pairWord, q.d⟩

theorem bitLane_wordStep (j r s : Nat) (message k : UInt256) (q : WordLane) :
    bitLane (wordStep j r s message k q) =
      pairedStep j r s (bits message) (bits k) (bitLane q) := by
  cases q
  unfold bitLane wordStep pairedStep
  simp only [bits_wordT, bits_land, bits_wordShift _ 22 (by decide),
    pairWord, bits_word, normalize_eq_and]

#print axioms bitLane_wordStep

def packCrypto (l q : PairedLaneCryptoBridge.CryptoLane) : WordLane :=
  liftLane (packLane (PairedLaneCryptoBridge.bits l) (PairedLaneCryptoBridge.bits q))

theorem wordStep_of_crypto (j r s : Nat)
    (hr0 : 0 < r) (hr : r < 32) (hs0 : 0 < s) (hs : s < 32)
    (wl wr kl kr : UInt32) (l q : PairedLaneCryptoBridge.CryptoLane) :
    wordStep j r s (word (pack wl.toBitVec wr.toBitVec))
        (word (pack kl.toBitVec kr.toBitVec)) (packCrypto l q) =
      packCrypto (PairedLaneCryptoBridge.cryptoStep j r wl kl l)
        (PairedLaneCryptoBridge.cryptoStep (4 - j) s wr kr q) := by
  apply bitLane_injective
  rw [bitLane_wordStep]
  simp only [packCrypto, bitLane_liftLane, bits_word]
  exact PairedLaneCryptoBridge.pairedStep_of_crypto j r s hr0 hr hs0 hs wl wr kl kr l q

#print axioms bitLane_liftLane
#print axioms wordStep_of_crypto

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRound
