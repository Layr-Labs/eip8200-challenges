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

private theorem wide_window (x : Nat) :
    (x*((2^32+1)*(2^6+2^72))%2^256)/2^28%2^32 =
      (x*(2^32+1)%2^256)/2^22%2^32 := by
  rw [Paired144Nat.truncate_window _ 28 32 256 (by decide),
    Paired144Nat.truncate_window _ 22 32 256 (by decide),
    ← Nat.mul_assoc, Nat.mul_add,
    Paired144Nat.div_pow_add_mul_pow _ _ 28 72 (by decide),
    Paired144Nat.mod_pow_add_mul_pow _ _ (72-28) 32 (by decide),
    Paired144Nat.mul_pow_div_pow _ 6 28 (by decide)]

private theorem low_shift_nat (x : BitVec 256) (n : Nat) :
    (low (x >>> n)).toNat = x.toNat / 2^n % 2^32 := by
  simp only [low, BitVec.extractLsb'_toNat, Nat.pow_zero, Nat.div_one,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem low_product_nat (x c : BitVec 256) (value n : Nat) (hc : c.toNat=value) :
    (low ((x*c) >>> n)).toNat = (x.toNat*value%2^256)/2^n%2^32 :=
  (low_shift_nat (x*c) n).trans
    (congrArg (fun z : Nat => z/2^n%2^32)
      ((BitVec.toNat_mul x c).trans
        (congrArg (fun z : Nat => x.toNat*z%2^256) hc)))

private theorem coefficient_nat : Paired144LegacyProduct.coefficient.toNat =
    (2^32+1)*(2^6+2^72) := by decide
private theorem factor_nat : factor.toNat = 2^32+1 := by decide

theorem wide_low_eq (x : BitVec 256) :
    low ((x * Paired144LegacyProduct.coefficient) >>> 28) = low ((x * factor) >>> 22) := by
  apply BitVec.eq_of_toNat_eq
  exact (low_product_nat x Paired144LegacyProduct.coefficient _ 28 coefficient_nat).trans
    ((wide_window x.toNat).trans (low_product_nat x factor _ 22 factor_nat).symm)

theorem low_rotate (x : BitVec 256) (hx : Low54 x) :
    low ((x * Paired144LegacyProduct.coefficient) >>> 28) = (low x).rotateLeft 10 := by
  rw [wide_low_eq, low_product_shift_eq x (pack (low x) 0#32) hx,
    ← wide_low_eq (pack (low x) 0#32)]
  exact StaggerScalarWide.low_rotate (low x) 0#32 10 (by decide) (by decide)

theorem low_word_rotate (c : UInt256) (hc : Low54 (bits c)) :
    low (bits (wordShift c 28)) = (low (bits c)).rotateLeft 10 := by
  rw [bits_wordShift _ 28 (by decide)]
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

theorem pairMask_low54 (x : UInt256) :
    Low54 (bits (UInt256.land x Paired144WordRound.pairWord)) := by
  rw [bits_land, Paired144WordRound.pairWord, bits_word, ← Paired144Core.normalize_eq_and]
  exact pack_low54 _ _

theorem project_step (maskB maskD : Bool) (j r : Nat) (hr0 : 0 < r) (hr : r < 17)
    (message k : UInt256) (q : WordLane) (hc : Low54 (bits q.c)) :
    unpackLeft (step maskB maskD j r message k q) =
      Paired80CryptoBridge.cryptoStep j r (low32 message) (low32 k) (unpackLeft q) := by
  have ht := low_t_bits maskB j r hr0 hr message k q
  have hd := (low_optional_mask maskD (wordShift q.c 28)).trans (low_word_rotate q.c hc)
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
