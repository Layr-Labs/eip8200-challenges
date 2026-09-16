import Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuardLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputData
import EvmSemantics.EVM.Step

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-!
# Arithmetic behind the entry dispatch

The size gate multiplies `size ^ 1000` by `size >> 2`; for realizable calldata
neither factor exceeds `2 ^ 64`, so the product is zero exactly when the input
is shorter than four bytes or exactly 1000 bytes long.  The tiny-input arm's
word test cannot succeed for a 1000-byte input or for an input whose first byte
is 7.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryGateLogic

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open TinyGuardLogic

def gateWord (n : Nat) : UInt256 :=
  UInt256.xor (UInt256.ofNat 1028) (UInt256.ofNat n) *
    UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat 2)

theorem xor_toNat (a b : UInt256) : (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  have ha := a.val.isLt
  have hb := b.val.isLt
  change ((a.toNat ^^^ b.toNat) % UInt256.size) = a.toNat ^^^ b.toNat
  apply Nat.mod_eq_of_lt
  exact Nat.xor_lt_two_pow ha hb

theorem gateWord_toNat (n : Nat) (hn : n < 2 ^ 64) :
    (gateWord n).toNat = (1000 ^^^ n) * (n / 4) := by
  have hn256 : n < 2 ^ 256 := Nat.lt_trans hn (by norm_num)
  have hx : 1000 ^^^ n < 2 ^ 64 := Nat.xor_lt_two_pow (by norm_num) hn
  have hxor : (UInt256.xor (UInt256.ofNat 1028) (UInt256.ofNat n)).toNat = 1000 ^^^ n := by
    rw [xor_toNat, Word.word_toNat_ofNat, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hn256]
  have hshift : (UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat 2)).toNat = n / 4 := by
    rw [Word.shiftRight_toNat _ (by decide), Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hn256, Nat.shiftRight_eq_div_pow]
  have hprod : (1000 ^^^ n) * (n / 4) < 2 ^ 256 := by
    have hq : n / 4 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self n 4) hn
    calc (1000 ^^^ n) * (n / 4) < 2 ^ 64 * 2 ^ 64 :=
          Nat.mul_lt_mul_of_lt_of_lt hx hq
      _ < 2 ^ 256 := by norm_num
  change ((UInt256.xor (UInt256.ofNat 1028) (UInt256.ofNat n)).toNat *
      (UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat 2)).toNat) % UInt256.size = _
  rw [hxor, hshift]
  exact Nat.mod_eq_of_lt hprod

theorem gateWord_true (n : Nat) (hn : n < 2 ^ 64) (h4 : 4 ≤ n) (h1000 : n ≠ 1000) :
    UInt256.isTrue (gateWord n) := by
  unfold UInt256.isTrue
  rw [gateWord_toNat n hn]
  have hx : 1000 ^^^ n ≠ 0 := by
    intro hz
    have hw : UInt256.xor (UInt256.ofNat 1028) (UInt256.ofNat n) = 0 := by
      apply Word.word_ext
      rw [xor_toNat, Word.word_toNat_ofNat, Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt (Nat.lt_trans hn (by norm_num)), hz]
      rfl
    have he := congrArg UInt256.toNat ((KnownInputLogic.wordXor_eq_zero_iff _ _).mp hw)
    rw [Word.word_toNat_ofNat, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt (Nat.lt_trans hn (by norm_num))] at he
    exact h1000 he.symm
  have hq : n / 4 ≠ 0 := by omega
  exact Nat.mul_ne_zero hx hq

theorem gateWord_false (n : Nat) (hn : n < 2 ^ 64) (h : n < 4 ∨ n = 1000) :
    ¬ UInt256.isTrue (gateWord n) := by
  unfold UInt256.isTrue
  rw [gateWord_toNat n hn, not_not]
  rcases h with h | h
  · have hq : n / 4 = 0 := by omega
    rw [hq, Nat.mul_zero]
  · subst h
    rfl

/-- The tiny-input arm's word test. -/
def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (leadWord input)
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621))

theorem leadWord_lt (input : ByteArray) : (leadWord input).toNat < 2 ^ 24 := by
  rw [prefix_toNat]
  have b0 := (byte input 0).toNat_lt
  have b1 := (byte input 1).toNat_lt
  have b2 := (byte input 2).toNat_lt
  omega

theorem mul_size_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621)).toNat =
      input.size * 0x207621 := by
  have hs : input.size < 2 ^ 64 := hfit
  change ((UInt256.ofNat input.size).toNat * (UInt256.ofNat 0x207621).toNat) % UInt256.size = _
  rw [Word.word_toNat_ofNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (show input.size < 2 ^ 256 by omega),
    Nat.mod_eq_of_lt (show (0x207621 : Nat) < 2 ^ 256 by norm_num)]
  apply Nat.mod_eq_of_lt
  unfold UInt256.size
  omega

theorem wordCond_ne_zero_iff (input : ByteArray) (hfit : CalldataFits input) :
    wordCond input = 0 ↔ (leadWord input).toNat = input.size * 0x207621 := by
  unfold wordCond
  rw [KnownInputLogic.wordXor_eq_zero_iff]
  constructor
  · intro h
    rw [h, mul_size_toNat input hfit]
  · intro h
    apply Word.word_ext
    rw [h, mul_size_toNat input hfit]

theorem wordCond_ne_zero_of_size1000 (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 1000) : wordCond input ≠ 0 := by
  intro hz
  have h := (wordCond_ne_zero_iff input hfit).mp hz
  have hl := leadWord_lt input
  omega

theorem wordCond_ne_zero_of_byte7 (input : ByteArray) (hfit : CalldataFits input)
    (hbyte : (byte input 0).toNat = 7) : wordCond input ≠ 0 := by
  intro hz
  have h := (wordCond_ne_zero_iff input hfit).mp hz
  rw [prefix_toNat, hbyte] at h
  have b1 := (byte input 1).toNat_lt
  have b2 := (byte input 2).toNat_lt
  rcases Nat.eq_zero_or_pos input.size with hs | hs
  · rw [hs] at h
    omega
  · have : input.size * 0x207621 ≥ 0x207621 := Nat.le_mul_of_pos_left _ hs
    omega

theorem wordCond_zero_size_pos (input : ByteArray) (hfit : CalldataFits input)
    (hpos : 0 < input.size) (hsmall : input.size < 4) (hz : wordCond input = 0) :
    input = AbcInputData.abcInput := by
  have hc : condition input = 0 := by
    change UInt256.lor (wordCond input) (UInt256.shiftRight (UInt256.ofNat input.size) (UInt256.ofNat 2)) = 0
    rw [hz]
    apply Word.word_ext
    rw [Word.word_toNat_lor, Word.shiftRight_toNat _ (by decide), Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hsmall (by norm_num)), Nat.shiftRight_eq_div_pow]
    have hq : input.size / 2 ^ 2 = 0 := by omega
    rw [hq]
    rfl
  rcases zero_cases input hfit hc with he | ha
  · rw [he] at hpos
    exact absurd hpos (by decide)
  · exact ha

/-- A calldata word of an input shorter than 32 bytes has a zero low byte, so it
is never the repeated `0x61` word. -/
theorem readWord_ne_fullWord (input : ByteArray) (hsize : input.size < 32) :
    MachineState.readWord input 0 ≠ KnownInputData.fullWord := by
  intro h
  have hn := congrArg UInt256.toNat h
  rw [Bytes.readWord_toNat, Bytes.bytesToNatPadded_succ] at hn
  have hz : (YulSemantics.EVM.byteFrom input.toList (0 + 31)).toNat = 0 := by
    have hb := byte_getD input 31
    change YulSemantics.EVM.byteFrom input.toList 31 = _ at hb
    rw [show 0 + 31 = 31 from rfl, hb,
      Memory.getElem?_getD_eq_zero_of_size_le input 31 (by omega)]
    rfl
  rw [hz, Nat.add_zero] at hn
  have hmod := congrArg (· % 256) hn
  simp only [Nat.mul_mod_left] at hmod
  revert hmod
  unfold KnownInputData.fullWord
  rw [Word.word_toNat_ofNat]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryGateLogic
