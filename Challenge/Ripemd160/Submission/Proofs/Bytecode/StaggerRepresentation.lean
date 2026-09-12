import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreModel
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRepresentation
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof PairedLaneUInt256Bridge Paired144Core
open Paired144WordRound Paired144WordRotation
open Paired80Compression (low32 unpackLeft)

open StaggerScalarWord (embed Clean)

theorem toNat_pack_zero_right (x : BitVec 32) : (pack x 0#32).toNat=x.toNat := by
  simp only [pack_toNat, BitVec.toNat_zero, Nat.zero_mul, Nat.add_zero]

theorem word_ofUInt32 (x : UInt32) : Word.ofUInt32 x = word (pack x.toBitVec 0#32) := by
  apply bits_injective
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 256 x.toNat).toNat = (pack x.toBitVec 0#32).toNat
  rw [BitVec.toNat_ofNat, toNat_pack_zero_right]
  exact Nat.mod_eq_of_lt (Nat.lt_trans x.toBitVec.isLt (by decide))

theorem pairWord_embed (a b : UInt32) :
    StaggerCoreModel.pairWord (word (pack a.toBitVec 0#32)) (word (pack b.toBitVec 0#32)) =
      StaggerAlgorithm.packed32 a b := by
  apply bits_injective
  rw [StaggerCoreModel.pairWord, bits_lor, bits_shl _ 144 (by decide)]
  simp only [bits_word, StaggerAlgorithm.packed32]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, toNat_pack_zero_right,
    toNat_pack_zero_right, pack_toNat]
  have ha : a.toNat < 2 ^ 144 := Nat.lt_trans a.toBitVec.isLt (by decide)
  have hb : b.toNat < 2 ^ 32 := b.toBitVec.isLt
  have hwide : b.toNat <<< 144 < 2 ^ 256 := by rw [Nat.shiftLeft_eq]; omega
  change b.toNat <<< 144 % 2^256 ||| a.toNat = a.toNat + b.toNat * 2^144
  rw [Nat.mod_eq_of_lt hwide, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq]
  omega

theorem pair_embed (a b : CryptoLane) :
    StaggerCoreModel.pair (embed a) (embed b) = packCrypto a b := by
  cases a; cases b
  simp only [StaggerCoreModel.pair, embed, packCrypto, show (0:UInt32).toBitVec = 0#32 from rfl]
  rw [pairWord_embed, pairWord_embed, pairWord_embed, pairWord_embed, pairWord_embed]
  rfl

theorem mask_packWord (a b : BitVec 32) :
    StaggerScalarWord.mask (word (pack a b)) = word (pack a 0#32) := by
  apply bits_injective
  rw [StaggerScalarWord.bits_mask, bits_word, bits_word, StaggerScalar.mask_eq, low_pack]

theorem left_packCrypto (a b : CryptoLane) :
    StaggerCoreModel.left (packCrypto a b) = packCrypto a b := by rfl

theorem clean_c (q : WordLane) (hq : Clean q) : StaggerScalarWord.mask q.c = q.c := by
  apply bits_injective
  rw [StaggerScalarWord.bits_mask]
  exact hq.2.2.1

theorem clean_b (q : WordLane) (hq : Clean q) : StaggerScalarWord.mask q.b = q.b := by
  apply bits_injective
  rw [StaggerScalarWord.bits_mask]
  exact hq.2.1

theorem clean_step_of_crypto (j r : Nat) (hr0 : 0 < r) (hr : r < 17)
    (message k : UInt256) (q : CryptoLane) :
    StaggerScalarWord.step true true j r message k (embed q) =
      embed (Paired80CryptoBridge.cryptoStep j r (low32 message) (low32 k) q) := by
  have hclean := StaggerScalarWord.step_clean j r message k (embed q) (StaggerScalarWord.embed_clean q)
  rw [StaggerScalarWord.clean_eq_embed _ hclean,
    StaggerScalarWord.project_step true true j r hr0 hr message k (embed q)
      (clean_c _ (StaggerScalarWord.embed_clean q))]
  rw [show unpackLeft (embed q) = q from StaggerScalarWord.unpackLeft_packCrypto _ _]

def initialCrypto (h : Compression.HashState) : CryptoLane :=
  PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h)

theorem initial_eq (memory : ByteArray) (h : Compression.HashState)
    (hh : StackMemory.hashAt memory = Compression.embedHash h) :
    StaggerCoreModel.initial memory = embed (initialCrypto h) := by
  have h0 := congrArg Compression.EvmHashState.h0 hh
  have h1 := congrArg Compression.EvmHashState.h1 hh
  have h2 := congrArg Compression.EvmHashState.h2 hh
  have h3 := congrArg Compression.EvmHashState.h3 hh
  have h4 := congrArg Compression.EvmHashState.h4 hh
  simp only [StackMemory.hashAt, Compression.embedHash] at h0 h1 h2 h3 h4
  simp only [StaggerCoreModel.initial, h0,h1,h2,h3,h4, word_ofUInt32]
  rfl

#print axioms pair_embed
#print axioms left_packCrypto
#print axioms clean_step_of_crypto
#print axioms initial_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRepresentation
