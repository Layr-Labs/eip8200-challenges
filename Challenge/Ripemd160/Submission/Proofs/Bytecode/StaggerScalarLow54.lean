import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarWord
set_option warningAsError true
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarLow54
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired80Product
open Paired144WordRound (WordLane packCrypto wordShift)
open Paired80Compression (low32 unpackLeft)
open StaggerScalarWide (bits_wordShift)
open StaggerScalarWord

def Low54 (x : BitVec 256) : Prop :=
  x.setWidth 54 = (pack (low x) 0#32).setWidth 54

theorem low_product_shift_eq (x y : BitVec 256)
    (h : x.setWidth 54 = y.setWidth 54) :
    low ((x * factor) >>> 22) = low ((y * factor) >>> 22) := by
  have hp : (x * factor).setWidth 54 = (y * factor).setWidth 54 := by
    rw [BitVec.setWidth_mul _ _ (by decide), BitVec.setWidth_mul _ _ (by decide), h]
  have hh := congrArg (fun z : BitVec 54 => z.extractLsb' 22 32) hp
  rw [BitVec.extractLsb'_setWidth_of_le (by decide),
    BitVec.extractLsb'_setWidth_of_le (by decide)] at hh
  change ((x * factor) >>> 22).setWidth 32 = ((y * factor) >>> 22).setWidth 32
  simpa only [BitVec.setWidth_ushiftRight_eq_extractLsb] using hh

theorem wide_low_eq (x : BitVec 256) :
    low ((x * RootCommonFactorPlusProduct.coefficient) >>> 23) = low ((x * factor) >>> 22) := by
  exact RootCommonFactorPlusScalar.wide_low_eq x

theorem low_rotate (x : BitVec 256) (hx : Low54 x) :
    low ((x * RootCommonFactorPlusProduct.coefficient) >>> 23) = (low x).rotateLeft 10 := by
  exact RootCommonFactorPlusScalar.low_rotate_low54 x hx

theorem low_word_rotate (c : UInt256) (hc : Low54 (bits c)) :
    low (bits (wordShift c 23)) = (low (bits c)).rotateLeft 10 := by
  rw [bits_wordShift _ 23 (by decide)]
  exact low_rotate _ hc

theorem pack_low54 (a b : BitVec 32) : Low54 (pack a b) := by
  unfold Low54
  rw [low_pack]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h144 : i < 144 := by omega
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    pack, BitVec.getLsbD_append, h144, ite_true]

theorem clean_low54 (c : UInt256) (hc : mask c = c) : Low54 (bits c) := by
  have h := congrArg bits hc
  rw [bits_mask, StaggerScalar.mask_eq] at h
  exact congrArg (fun x : BitVec 256 => x.setWidth 54) h.symm

theorem project_step (maskB maskD : Bool) (j r : Nat) (hr0 : 0 < r) (hr : r < 17)
    (message k : UInt256) (q : WordLane) (hc : Low54 (bits q.c)) :
    unpackLeft (step maskB maskD j r message k q) =
      Paired80CryptoBridge.cryptoStep j r (low32 message) (low32 k) (unpackLeft q) := by
  have ht := low_t_bits maskB j r hr0 hr message k q
  have hd := (low_optional_mask maskD (wordShift q.c 23)).trans (low_word_rotate q.c hc)
  apply crypto_bits_inj
  rw [Paired80CryptoBridge.cryptoStep_bits j r hr0 hr]
  exact congrArg₂ (fun b d : BitVec 32 =>
    (⟨low (bits q.e), b, low (bits q.b), d, low (bits q.d)⟩ : Paired80RoundSemantic.Lane 32)) ht hd

theorem packCrypto_low54 (l r : Paired80CryptoBridge.CryptoLane) :
    Low54 (bits (packCrypto l r).a) ∧ Low54 (bits (packCrypto l r).b) ∧
    Low54 (bits (packCrypto l r).c) ∧ Low54 (bits (packCrypto l r).d) ∧
    Low54 (bits (packCrypto l r).e) := by
  constructor
  · change Low54 (bits (word (pack _ _)))
    rw [bits_word]
    exact pack_low54 _ _
  constructor
  · change Low54 (bits (word (pack _ _)))
    rw [bits_word]
    exact pack_low54 _ _
  constructor
  · change Low54 (bits (word (pack _ _)))
    rw [bits_word]
    exact pack_low54 _ _
  constructor
  all_goals
    change Low54 (bits (word (pack _ _)))
    rw [bits_word]
    exact pack_low54 _ _

#print axioms pack_low54
#print axioms clean_low54
#print axioms project_step
#print axioms packCrypto_low54
#print axioms wide_low_eq
#print axioms low_product_shift_eq
#print axioms low_rotate
#print axioms low_word_rotate
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarLow54
