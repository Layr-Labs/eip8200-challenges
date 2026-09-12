import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentTailBinding

open EvmSemantics Challenge.EvmProof.Word
open PairedLaneUInt256Bridge Paired144Core Paired144WordRound

def combine (h : Compression.HashState) (q : WordLane) : Compression.HashState :=
  {h0 := h.h1 + toUInt32 q.c + PersistentFrame.high q.d,
   h1 := h.h2 + toUInt32 q.d + PersistentFrame.high q.e,
   h2 := h.h3 + toUInt32 q.e + PersistentFrame.high q.a,
   h3 := h.h4 + toUInt32 q.a + PersistentFrame.high q.b,
   h4 := h.h0 + toUInt32 q.b + PersistentFrame.high q.c}

def normalizeWord (x : UInt256) : UInt256 := word (normalize (bits x))
def normalizeLane (q : WordLane) : WordLane :=
  ⟨normalizeWord q.a, normalizeWord q.b, normalizeWord q.c,
    normalizeWord q.d, normalizeWord q.e⟩

theorem low_bits (x : UInt256) : (toUInt32 x).toBitVec = low (bits x) := by
  apply BitVec.eq_of_toNat_eq
  change (toUInt32 x).toNat = (low (bits x)).toNat
  rw [toUInt32_toNat]
  simp only [low, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, bits_toNat]

theorem high_bits (x : UInt256) : (PersistentFrame.high x).toBitVec = high (bits x) := by
  rw [PersistentFrame.high, low_bits, bits_shr x 144 (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [low, high, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]

@[simp] theorem low_normalize (x : UInt256) : toUInt32 (normalizeWord x) = toUInt32 x := by
  apply UInt32.eq_of_toBitVec_eq
  rw [low_bits, low_bits, normalizeWord, bits_word, normalize, low_pack]

@[simp] theorem high_normalize (x : UInt256) :
    PersistentFrame.high (normalizeWord x) = PersistentFrame.high x := by
  apply UInt32.eq_of_toBitVec_eq
  rw [high_bits, high_bits, normalizeWord, bits_word, normalize, high_pack]

theorem combine_normalize (h : Compression.HashState) (q : WordLane) :
    combine h (normalizeLane q) = combine h q := by
  simp only [combine, normalizeLane, low_normalize, high_normalize]

@[simp] theorem low_packed (a b : UInt32) : toUInt32 (word (pack a.toBitVec b.toBitVec)) = a := by
  apply UInt32.eq_of_toBitVec_eq
  rw [low_bits, bits_word, low_pack]

@[simp] theorem high_packed (a b : UInt32) :
    PersistentFrame.high (word (pack a.toBitVec b.toBitVec)) = b := by
  apply UInt32.eq_of_toBitVec_eq
  rw [high_bits, bits_word, high_pack]

theorem combine_packCrypto (h : Compression.HashState) (l r : CryptoLane) :
    combine h (packCrypto l r) =
      {h0 := h.h1 + l.c + r.d, h1 := h.h2 + l.d + r.e,
       h2 := h.h3 + l.e + r.a, h3 := h.h4 + l.a + r.b,
       h4 := h.h0 + l.b + r.c} := by
  simp only [combine, packCrypto, low_packed, high_packed]

#print axioms low_bits
#print axioms high_bits
#print axioms combine_normalize
#print axioms combine_packCrypto

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentTailBinding
